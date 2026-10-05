import CartexpAristotle.ColaxSliceCartAdjunction
import CartexpAristotle.ColaxSliceCartExponentiable
import CartexpAristotle.AdjointExp

/-!
# `ColaxSliceCart.toOver` preserves the exponentiable arrow `UFam`

We check the Frobenius condition for the adjunction `ofOver ⊣ toOver` and the arrow `UFam`:
the pullback in `Over (Cat.of Fam)` of `toOver.map UFam` along `f : d ⟶ toOver.obj SetObj` is the
category of elements of `x ↦ (f x).obj`, and its image under `ofOver` is exactly the chosen
pullback `pbChosen` of `UFam` in `ColaxSliceCart`.

## References

* [Paper, App. A.4, proof of Prop. `prop:semantic-twosort-functor`], last condition: "the
  naturality square of the counit for the exponentiable morphism is a pullback", here phrased as
  a Frobenius condition for the adjunction `ofOver ⊣ toOver` (`frobenius_UFam`).
-/

universe w

open CategoryTheory Limits ColaxSliceCart ColaxSliceCartExponentiable PointedForget

namespace SemanticTwoSortFrobenius

lemma heq_right_of_heq {X : ColaxSliceCart.{w, w, w + 1}} {a a' b b' : CartComma X} (ha : a = a')
    (hb : b = b') {φ : a ⟶ b} {ψ : a' ⟶ b'} (h : HEq φ ψ) :
    HEq (φ : CartComma.Hom a b).right (ψ : CartComma.Hom a' b').right := by
  subst ha hb
  obtain rfl := eq_of_heq h
  rfl

/-- The image of `toOver.map UFam` in `Cat`. -/
abbrev RU : Cat.of (CartComma PtObj.{w}) ⟶ Cat.of (CartComma SetObj.{w}) :=
  (CartComma.map UFam.{w}).toCatHom

lemma cartPt_ext {a b : CartComma PtObj.{w}} (h₁ : a.obj = b.obj)
    (h₂ : (CartComma.map UFam).obj a = (CartComma.map UFam).obj b) : a = b := by
  rcases a with ⟨ao, at', ah, _⟩
  rcases b with ⟨bo, bt, bh, _⟩
  dsimp only at h₁
  subst h₁
  have ht : at' = bt := congrArg CartComma.tgt h₂
  subst ht
  have hh : HEq ah bh := by
    have := congr_arg_heq CartComma.hom h₂
    exact this
  obtain rfl := eq_of_heq hh
  rfl

variable {d : Over (Cat.of Fam.{w})} (f : d ⟶ toOver.obj SetObj.{w})

/-- The functor `x ↦ (f x).obj` from `d` to types. -/
abbrev fSet : d.left ⥤ Type w := f.left.toFunctor ⋙ CartComma.objFunctor SetObj.{w}

/-- The first projection of the pullback, as a functor. -/
def p1Functor : (fSet f).Elements ⥤ CartComma PtObj.{w} where
  obj x := ⟨(elToPt (fSet f)).obj x, (f.left.toFunctor.obj x.1).tgt,
    (f.left.toFunctor.obj x.1).hom, (f.left.toFunctor.obj x.1).isCartesian⟩
  map {x y} φ := ⟨(elToPt (fSet f)).map φ, (f.left.toFunctor.map φ.1 : CartComma.Hom _ _).right,
    (f.left.toFunctor.map φ.1 : CartComma.Hom _ _).w⟩
  map_id x := by
    have h := f.left.toFunctor.map_id x.1
    exact CartComma.Hom.ext ((elToPt (fSet f)).map_id x) (congrArg (@CartComma.Hom.right SetObj.{w} _ _) h)
  map_comp φ ψ := by
    have h := f.left.toFunctor.map_comp φ.1 ψ.1
    exact CartComma.Hom.ext ((elToPt (fSet f)).map_comp φ ψ) (congrArg (@CartComma.Hom.right SetObj.{w} _ _) h)

lemma p1_condition : (p1Functor f).toCatHom ≫ RU = (CategoryOfElements.π (fSet f)).toCatHom ≫ f.left :=
  rfl

section Lift

variable {f} (s : PullbackCone RU.{w} f.left)

lemma lift_cond : (s.fst.toFunctor ⋙ CartComma.objFunctor PtObj.{w}) ⋙ forget Pointed.{w} =
    s.snd.toFunctor ⋙ fSet f :=
  congrArg (fun F => F ⋙ CartComma.objFunctor SetObj.{w}) (congrArg Cat.Hom.toFunctor s.condition)

/-- The lift into the pullback. -/
def pbLift : s.pt ⟶ Cat.of (fSet f).Elements :=
  (elLift (s.fst.toFunctor ⋙ CartComma.objFunctor PtObj.{w}) s.snd.toFunctor (lift_cond s)).toCatHom

lemma pbLift_fst : pbLift s ≫ (p1Functor f).toCatHom = s.fst := by
  have hc := congrArg Cat.Hom.toFunctor s.condition
  have hp := elLift_fac_left (s.fst.toFunctor ⋙ CartComma.objFunctor PtObj.{w}) s.snd.toFunctor
    (lift_cond s)
  have hobj : ∀ y, (elLift _ _ (lift_cond s) ⋙ p1Functor f).obj y = s.fst.toFunctor.obj y :=
    fun y => cartPt_ext (Functor.congr_obj hp y) (Functor.congr_obj hc y).symm
  refine Cat.Hom.ext (Functor.hext hobj (fun y y' g => ?_))
  refine CartComma.Hom.hext (hobj y) (hobj y') (Functor.hcongr_hom hp g) ?_
  exact (heq_right_of_heq (Functor.congr_obj hc y) (Functor.congr_obj hc y')
    (Functor.hcongr_hom hc g)).symm

lemma pbLift_snd : pbLift s ≫ (CategoryOfElements.π (fSet f)).toCatHom = s.snd := rfl

lemma pbLift_uniq (m : s.pt ⟶ Cat.of (fSet f).Elements) (h₁ : m ≫ (p1Functor f).toCatHom = s.fst)
    (h₂ : m ≫ (CategoryOfElements.π (fSet f)).toCatHom = s.snd) : m = pbLift s :=
  Cat.Hom.ext (elLift_uniq _ _ _ m.toFunctor
    (congrArg (fun F => F.toFunctor ⋙ CartComma.objFunctor PtObj.{w}) h₁)
    (congrArg Cat.Hom.toFunctor h₂))

end Lift

lemma isPullback_cat : IsPullback (p1Functor f).toCatHom (CategoryOfElements.π (fSet f)).toCatHom
    RU.{w} f.left :=
  IsPullback.of_isLimit (PullbackCone.IsLimit.mk (p1_condition f) pbLift pbLift_fst pbLift_snd
    pbLift_uniq)

/-- The pullback of `toOver.map UFam` along `f`, as an object of `Over (Cat.of Fam)`. -/
def K0obj : Over (Cat.of Fam.{w}) :=
  Over.mk ((CategoryOfElements.π (fSet f)).toCatHom ≫ d.hom)

/-- The first projection of the pullback in `Over (Cat.of Fam)`. -/
def K0p₁ : K0obj f ⟶ toOver.obj PtObj.{w} :=
  Over.homMk (p1Functor f).toCatHom (by
    change (CategoryOfElements.π (fSet f)).toCatHom ≫ f.left ≫ (toOver.obj SetObj.{w}).hom = _
    rw [Over.w f]
    rfl)

/-- The second projection of the pullback in `Over (Cat.of Fam)`. -/
def K0p₂ : K0obj f ⟶ d :=
  Over.homMk (CategoryOfElements.π (fSet f)).toCatHom rfl

lemma K0_isPullback : IsPullback (K0p₁ f) (K0p₂ f) (toOver.map UFam.{w}) f :=
  IsPullback.of_map (Over.forget _) (Over.OverMorphism.ext (p1_condition f)) (isPullback_cat f)

/-- The chosen pullback of `toOver.map UFam` along `f`. -/
noncomputable def K0 : ChosenPullback (toOver.map UFam.{w}) f :=
  SliceExp.chosenOfIsPullback (K0_isPullback f)

lemma K0_fst : (ofOverAdj.homEquiv _ _).symm (K0 f).p₁ =
    (pbFst ((ofOverAdj.homEquiv _ _).symm f) : ofOver.obj (K0obj f) ⟶ PtObj.{w}) := by
  rw [Adjunction.homEquiv_counit]
  refine Hom.ext_of_functor_eq rfl (fun x => ?_)
  change HEq ((Hom.comp _ _).nat.app x : Fam.Hom _ _).base
    (((ofOverAdj.homEquiv _ _).symm f).nat.app x.1 : Fam.Hom _ _).base
  refine HEq.trans ?_ (Hom.base_heq_of_eq (ofOverAdj.homEquiv_counit (g := f)) x.1).symm
  change HEq _ ((Hom.comp (ofOver.map f) (ofOverAdj.counit.app SetObj)).nat.app x.1 :
    Fam.Hom _ _).base
  simp only [Hom.comp, ofOver, NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app]
  rfl

lemma K0_snd : ofOver.map (K0 f).p₂ =
    (pbSnd ((ofOverAdj.homEquiv _ _).symm f) : ofOver.obj (K0obj f) ⟶ ofOver.obj d) := by
  exact Hom.ext_of_functor_eq rfl (fun x => HEq.rfl)

lemma K0_frob : IsPullback ((ofOverAdj.homEquiv _ _).symm (K0 f).p₁) (ofOver.map (K0 f).p₂)
    UFam.{w} ((ofOverAdj.homEquiv _ _).symm f) := by
  rw [K0_fst, K0_snd]
  exact (pbChosen ((ofOverAdj.homEquiv _ _).symm f)).isPullback

/-- The Frobenius condition for `ofOver ⊣ toOver` and `UFam`.

[Paper, App. A.4, proof of Prop. `prop:semantic-twosort-functor`]. -/
lemma frobenius_UFam : Frobenius ofOverAdj.{w} UFam.{w} :=
  Frobenius.of_chosen (fun f => K0 f) (fun f => K0_frob f)

/-- `toOver` preserves the exponentiable arrow `UFam`. -/
noncomputable instance toOver_preserves_UFam : FunctorPreserves UFam.{w} toOver.{w} :=
  functorPreserves_of_adjunction frobenius_UFam

end SemanticTwoSortFrobenius
