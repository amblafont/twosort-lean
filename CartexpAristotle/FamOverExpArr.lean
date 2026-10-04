import CartexpAristotle.FamOverFrobenius
import CartexpAristotle.CatPullbacks
import CartexpAristotle.ExpArrEndofunctor
import Mathlib.CategoryTheory.Category.Cat.Terminal

/-!
# `FamSlice.toOver` is a morphism of `ExpArrCat`

* `CatExp`: the category `Cat.{w, w+1}` with the exponentiable arrow `U : Pointed ⥤ Type w`.
* `FamSliceExp`: `FamSlice` with the exponentiable arrow `UFam`.
* The image `Φ CatExp` of `CatExp` under the endofunctor of `ExpArrCat` is the slice of `Cat` over
  the category of formal coproducts of types, which is isomorphic to `Fam` (`famFC`). Hence the
  slice `Over (Cat.of Fam)` inherits an `ExpArrCat` structure (`FamOverExp`) by transport along
  the equivalence `Over (Cat.of Fam) ≌ Over (Cat.of (FormalCoproduct (Type w)))`.
* `toOverHom : FamSliceExp ⟶ FamOverExp`: the functor `FamSlice.toOver` is a morphism of
  `ExpArrCat`. It preserves pullbacks and the terminal object (being a right adjoint), it preserves
  the exponentiable arrow (Frobenius condition), and it sends `UFam` to an arrow isomorphic to the
  chosen arrow of `FamOverExp`.
-/

universe w

open CategoryTheory Limits FamSlice FamPointedForget PointedForget FamOverFrobenius

namespace FamOverExpArr

/-! ### The objects of `ExpArrCat` -/

/-- `Cat.{w, w+1}` with the exponentiable arrow `U : Pointed ⥤ Type w`. -/
noncomputable def CatExp : ExpArrCat.{w + 1, w + 2} where
  carrier := Cat.{w, w + 1}
  arr := U.{w}

/-- `FamSlice` with the exponentiable arrow `UFam`. -/
noncomputable def FamSliceExp : ExpArrCat.{w + 1, w + 2} where
  carrier := FamSlice.{w, w, w + 1}
  arr := UFam.{w}

/-! ### `Fam` is isomorphic to the category of formal coproducts of types -/

/-- A family of types as a formal coproduct of types. -/
def famToFC : Fam.{w} ⥤ FormalCoproduct.{w} (Type w) where
  obj T := ⟨T.base, T.fiber⟩
  map φ := ⟨(φ : Fam.Hom _ _).base, (φ : Fam.Hom _ _).fiber⟩

/-- A formal coproduct of types as a family of types. -/
def fcToFam : FormalCoproduct.{w} (Type w) ⥤ Fam.{w} where
  obj X := ⟨X.I, X.obj⟩
  map g := ⟨g.f, g.φ⟩

/-- `Fam` is isomorphic to the category of formal coproducts of types. -/
def famFC : Cat.of Fam.{w} ≅ Cat.of (FormalCoproduct.{w} (Type w)) where
  hom := Functor.toCatHom famToFC.{w}
  inv := Functor.toCatHom fcToFam.{w}
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- The slice `Over (Cat.of Fam)` with the `ExpArrCat` structure inherited from `Φ CatExp`
along the isomorphism `famFC`. -/
noncomputable def FamOverExp : ExpArrCat.{w + 1, w + 2} :=
  ExpArrCat.ofEquivalence (ExpArrCat.Φobj.{w + 1, w + 2} CatExp.{w}) (Over (Cat.of Fam.{w}))
    (Over.mapIso famFC)

/-! ### The cartesian comma category of `SetObj` is the category of pointed families -/

/-- `(X, T, f) ↦ (T, f ⋆)`. -/
def csFunctor : CartComma SetObj.{w} ⥤ (idx.{w} (Type w)).Elements where
  obj a := ⟨famToFC.{w}.obj a.tgt, (a.hom : Fam.Hom _ _).base PUnit.unit⟩
  map {a b} φ := ⟨famToFC.{w}.map (φ : CartComma.Hom a b).right,
    (congrFun (congrArg Fam.Hom.base (φ : CartComma.Hom a b).w) PUnit.unit).symm⟩

/-- `(T, t) ↦ (T t, T, t)`. -/
def scFunctor : (idx.{w} (Type w)).Elements ⥤ CartComma SetObj.{w} where
  obj x := ⟨x.1.obj x.2, fcToFam.{w}.obj x.1, ⟨fun _ => x.2, fun _ y => y⟩, fun _ => ⟨rfl, fun _ => rfl⟩⟩
  map {x y} g := ⟨(eps.{w} (Type w)).map g, fcToFam.{w}.map g.1, by
    obtain ⟨X, i⟩ := x
    obtain ⟨Y, j⟩ := y
    obtain ⟨g, hg⟩ := g
    change X ⟶ Y at g
    obtain rfl : j = g.f i := hg.symm
    refine Fam.Hom.ext' rfl (fun _ z => ?_)
    change HEq ((g.φ i ≫ eqToHom rfl) z) (g.φ i z)
    rw [eqToHom_refl, Category.comp_id]⟩
  map_id x := by
    refine CartComma.Hom.ext ((eps.{w} (Type w)).map_id x) ?_
    exact fcToFam.{w}.map_id x.1
  map_comp f g := by
    refine CartComma.Hom.ext ((eps.{w} (Type w)).map_comp f g) ?_
    exact fcToFam.{w}.map_comp f.1 g.1

lemma setFam_hom_heq' {X Y : Type w} {T : Fam.{w}} (e : X = Y) (h : setFam.obj X ⟶ T)
    (h' : setFam.obj Y ⟶ T)
    (hb : (h : Fam.Hom _ _).base PUnit.unit = (h' : Fam.Hom _ _).base PUnit.unit)
    (hf : ∀ x y, HEq x y →
      HEq ((h : Fam.Hom _ _).fiber PUnit.unit x) ((h' : Fam.Hom _ _).fiber PUnit.unit y)) :
    HEq h h' := by
  subst e
  refine heq_of_eq (Fam.Hom.ext' (funext fun u => by cases u; exact hb) (fun u x => ?_))
  cases u
  exact hf x x HEq.rfl

lemma setFam_hom_heq {X : Type w} {T : Fam.{w}} (h : setFam.obj X ⟶ T) (hc : h.IsCartesian) :
    HEq h (⟨fun _ => (h : Fam.Hom _ _).base PUnit.unit, fun _ y => y⟩ :
      Fam.Hom (setFam.obj (T.fiber ((h : Fam.Hom _ _).base PUnit.unit))) T) :=
  setFam_hom_heq' (hc.fiber_eq PUnit.unit) h _ rfl
    (fun x _ hxy => (hc.fiber_heq PUnit.unit x).trans hxy)

lemma eqToHom_apply_heq {A B : Type w} (e : A = B) (y : A) : HEq ((eqToHom e : A ⟶ B) y) y := by
  subst e; rfl

lemma comp_eqToHom_apply_heq {A B B' : Type w} (f : A ⟶ B) (e : B = B') (y : A) :
    HEq ((f ≫ eqToHom e) y) (f y) := by
  subst e; rfl

lemma cs_sc_obj (a : CartComma SetObj.{w}) : scFunctor.obj (csFunctor.obj a) = a :=
  CartComma.ext' (a.isCartesian.fiber_eq PUnit.unit).symm rfl
    (setFam_hom_heq a.hom a.isCartesian).symm

lemma cs_sc : csFunctor.{w} ⋙ scFunctor.{w} = 𝟭 _ := by
  refine Functor.hext cs_sc_obj (fun a b φ => ?_)
  refine CartComma.Hom.hext (cs_sc_obj a) (cs_sc_obj b) ?_ HEq.rfl
  refine Function.hfunext (congrArg CartComma.obj (cs_sc_obj a)) (fun x x' hx => ?_)
  refine (comp_eqToHom_apply_heq _ _ _).trans ?_
  have hx' : x = (a.hom : Fam.Hom _ _).fiber PUnit.unit x' :=
    eq_of_heq (hx.trans ((a.isCartesian.fiber_heq PUnit.unit x').symm))
  refine HEq.trans ?_ ((b.isCartesian).fiber_heq PUnit.unit ((φ : CartComma.Hom a b).left x'))
  rw [hx']
  exact (Fam.Hom.congr_fiber (φ : CartComma.Hom a b).w PUnit.unit x').symm

lemma sc_cs : scFunctor.{w} ⋙ csFunctor.{w} = 𝟭 _ := rfl

/-- The cartesian comma category of `SetObj` is isomorphic to the category of elements of
`idx (Type w)`. -/
def rc : Cat.of (CartComma SetObj.{w}) ≅ Cat.of (idx.{w} (Type w)).Elements where
  hom := csFunctor.toCatHom
  inv := scFunctor.toCatHom
  hom_inv_id := Cat.Hom.ext cs_sc
  inv_hom_id := Cat.Hom.ext sc_cs

/-! ### The isomorphism of arrows -/

/-- The codomain of `toOver.map UFam` is isomorphic to the codomain of the chosen arrow. -/
noncomputable def isoR : toOver.obj SetObj.{w} ≅ (Over.map famFC.{w}.inv).obj (Over.mk (SliceExp.sW U.{w})) :=
  Over.isoMk rc rfl

/-- The comparison between the pullback `K0` along `isoR.inv` and the chosen pullback
`sY' U` of `Cat`. -/
noncomputable def isoφ : (K0obj isoR.{w}.inv).left ≅ SliceExp.sY' U.{w} :=
  (elChosen (SliceExp.sE U.{w})).isPullback.isoIsPullback _ _ (SliceExp.shpb U.{w})

lemma isoφ_snd : isoφ.{w}.hom ≫ SliceExp.su' U.{w} = (K0p₂ isoR.{w}.inv).left :=
  (elChosen (SliceExp.sE U.{w})).isPullback.isoIsPullback_hom_snd _ _ (SliceExp.shpb U.{w})

instance : IsIso (K0p₁ isoR.{w}.inv) := (K0_isPullback isoR.{w}.inv).isIso_fst_of_isIso

/-- The domain of `toOver.map UFam` is isomorphic to the domain of the chosen arrow. -/
noncomputable def isoL : toOver.obj PtObj.{w} ≅
    (Over.map famFC.{w}.inv).obj (Over.mk (SliceExp.su' U.{w} ≫ SliceExp.sW U.{w})) :=
  (asIso (K0p₁ isoR.{w}.inv)).symm ≪≫ Over.isoMk isoφ (by
    change isoφ.hom ≫ SliceExp.su' U ≫ SliceExp.sW U ≫ famFC.inv = _
    rw [← Category.assoc, isoφ_snd]
    rfl)

lemma isoL_comm : isoL.{w}.hom ≫ (Over.map famFC.{w}.inv).map (SliceExp.sArr U.{w}) =
    toOver.map UFam.{w} ≫ isoR.hom := by
  rw [← cancel_epi (K0p₁ isoR.{w}.inv)]
  have hc := (K0_isPullback isoR.{w}.inv).w
  rw [reassoc_of% hc, Iso.inv_hom_id, Category.comp_id]
  simp only [isoL, Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc, IsIso.hom_inv_id_assoc]
  exact Over.OverMorphism.ext isoφ_snd

/-! ### The morphism of `ExpArrCat` -/

/-- The functor `FamSlice.toOver` is a morphism of `ExpArrCat` from `FamSlice` (with the
exponentiable arrow `UFam`) to `Over (Cat.of Fam)` (with the structure inherited from `Φ CatExp`):
it preserves pullbacks, the terminal object and the exponentiable arrow, and sends `UFam` to an
arrow isomorphic to the chosen arrow. -/
noncomputable def toOverHom : FamSliceExp.{w} ⟶ FamOverExp.{w} where
  functor := toOver.{w}
  preservesPullbacks := (inferInstance : PreservesLimitsOfShape WalkingCospan toOver.{w})
  preservesTerminal := (inferInstance : PreservesLimitsOfShape (Discrete PEmpty.{1}) toOver.{w})
  preservesArr := toOver_preserves_UFam
  iso := Arrow.isoMk isoL isoR isoL_comm

lemma toOverHom_functor :
    (toOverHom.{w} : ExpArrCat.Hom FamSliceExp FamOverExp).functor = toOver.{w} := rfl

end FamOverExpArr
