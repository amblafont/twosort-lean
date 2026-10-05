import CartexpAristotle.CatExponentiable
import CartexpAristotle.ColaxSliceCartLimits

/-!
# The forgetful functor from pointed types is an exponentiable arrow in `ColaxSliceCart`

We equip `Type w` and `Pointed` with the functors to `Fam` sending a (pointed) type `X` to the
family with base `PUnit` and fibre `X`. The forgetful functor `Pointed ⥤ Type w`, together with
the identity natural transformation, is then a morphism `UFam` in `ColaxSliceCart`, lying over the
exponentiable arrow `PointedForget.U` of `Cat`. We show that `UFam` is again exponentiable.

## References

* [Paper, §4, Example `ex:main-thms`]: the family functors of sets and of pointed sets, sending
  `A` to the family `(A)_{* ∈ {*}}` (`setFam`, `ptFam`).
* [Paper, §4.1, Thm. `thm:colax-exponentiable`] and [Paper, App. A.4, Prop.
  `prop:cartesian-colax-lexp`]: the forgetful functor `PtdSet → Set`, with the identity natural
  transformation between these family functors, is exponentiable in `CAT //_c Fam`
  (`UFam`, `expData`, `expUniversal`).
-/

open CategoryTheory Limits ColaxSliceCart PointedForget

universe w

namespace ColaxSliceCartExponentiable

/-- A type `X`, viewed as the family with base `PUnit` and fibre `X`.

[Paper, §4, Example `ex:main-thms`]: the family functor of sets. -/
def setFam : Type w ⥤ Fam.{w} where
  obj X := ⟨PUnit, fun _ => X⟩
  map f := ⟨id, fun _ => f⟩

/-- A pointed type `X`, viewed as the family with base `PUnit` and fibre `X`.

[Paper, §4, Example `ex:main-thms`]: the family functor of pointed sets. -/
def ptFam : Pointed.{w} ⥤ Fam.{w} where
  obj X := ⟨PUnit, fun _ => X.X⟩
  map f := ⟨id, fun _ => f.toFun⟩

/-- The object `(Type w, setFam)` of `ColaxSliceCart`. -/
def SetObj : ColaxSliceCart.{w, w, w + 1} := ⟨Cat.of (Type w), setFam⟩

/-- The object `(Pointed, ptFam)` of `ColaxSliceCart`. -/
def PtObj : ColaxSliceCart.{w, w, w + 1} := ⟨Cat.of Pointed.{w}, ptFam⟩

/-- The forgetful functor `Pointed ⥤ Type w` as a morphism of `ColaxSliceCart`: its natural
transformation `U ⋙ setFam ⟶ ptFam` is the identity.

[Paper, §4.1, Thm. `thm:colax-exponentiable`]: the exponentiable morphism of `CAT //_c Fam`. -/
def UFam : PtObj.{w} ⟶ SetObj.{w} where
  functor := U.toFunctor
  nat :=
    { app _ := ⟨id, fun _ x => x⟩
      naturality _ _ _ := rfl }
  isPointwiseCartesian _ _ := ⟨rfl, fun _ => rfl⟩

/-- `UFam` lies over the exponentiable arrow `U` of `Cat`. -/
lemma UFam_functor : UFam.{w}.functor = U.{w}.toFunctor := rfl

/-! ### Chosen pullbacks along `UFam` -/

section Pullback

variable {D : ColaxSliceCart.{w, w, w + 1}} (h : D ⟶ SetObj.{w})

/-- The pullback of `UFam` along `h = (h₀, m)`: the category of elements of `h₀`, with the
family of `(d, a)` being the family of `d`. -/
def pbObj : ColaxSliceCart.{w, w, w + 1} :=
  ⟨Cat.of h.functor.Elements, CategoryOfElements.π h.functor ⋙ D.F⟩

/-- The first projection of the pullback. -/
def pbFst : pbObj h ⟶ PtObj.{w} where
  functor := elToPt h.functor
  nat :=
    { app x := h.nat.app x.1
      naturality _ _ f := h.nat.naturality f.1 }
  isPointwiseCartesian x := h.isPointwiseCartesian x.1

/-- The second projection of the pullback. -/
def pbSnd : pbObj h ⟶ D where
  functor := CategoryOfElements.π h.functor
  nat := 𝟙 _
  isPointwiseCartesian _ := Fam.Hom.isCartesian_id _

lemma pb_condition : pbFst h ≫ UFam = pbSnd h ≫ h :=
  Hom.ext_of_functor_eq rfl (fun _ => HEq.rfl)

variable {h}

section Lift

variable (s : PullbackCone UFam.{w} h)

lemma lift_functor_eq : s.fst.functor ⋙ forget Pointed = s.snd.functor ⋙ h.functor :=
  Hom.functor_eq_of_eq s.condition

/-- The map induced by a cone into the pullback. -/
def pbLift : s.pt ⟶ pbObj h where
  functor := elLift s.fst.functor s.snd.functor (lift_functor_eq s)
  nat :=
    { app q := s.snd.nat.app q
      naturality _ _ f := s.snd.nat.naturality f }
  isPointwiseCartesian q := s.snd.isPointwiseCartesian q

lemma pbLift_fst : pbLift s ≫ pbFst h = s.fst := by
  refine Hom.ext_of_functor_eq (elLift_fac_left _ _ _) (fun q => heq_of_eq ?_)
  have e := eq_of_heq (Hom.base_heq_of_eq s.condition q)
  exact e.symm

lemma pbLift_snd : pbLift s ≫ pbSnd h = s.snd :=
  Hom.ext_of_functor_eq rfl (fun _ => HEq.rfl)

lemma pbLift_uniq (m : s.pt ⟶ pbObj h) (h₁ : m ≫ pbFst h = s.fst) (h₂ : m ≫ pbSnd h = s.snd) :
    m = pbLift s :=
  Hom.ext_of_functor_eq
    (elLift_uniq _ _ _ m.functor (Hom.functor_eq_of_eq h₁) (Hom.functor_eq_of_eq h₂))
    (fun q => Hom.base_heq_of_eq h₂ q)

end Lift

variable (h) in
/-- The chosen pullback of `UFam` along `h`. -/
def pbChosen : ChosenPullback UFam.{w} h where
  pullback := pbObj h
  p₁ := pbFst h
  p₂ := pbSnd h
  condition := pb_condition h
  isLimit := PullbackCone.IsLimit.mk _ pbLift pbLift_fst pbLift_snd pbLift_uniq

end Pullback

/-! ### The partial exponential -/

section Exp

variable {C : Cat.{w, w + 1}} (G : C ⥤ Fam.{w})

/-- The index type of the family attached to a formal coproduct `X = ∐ a, X.obj a`: one index
for the indexing type `X.I` itself, plus the indices of all the families `G (X.obj a)`. -/
abbrev expBase (X : FormalCoproduct.{w} C) : Type w :=
  PUnit.{w + 1} ⊕ Σ a : X.I, (G.obj (X.obj a)).base

/-- The fibres of the family attached to a formal coproduct. -/
def expFiber (X : FormalCoproduct.{w} C) : expBase G X → Type w
  | .inl _ => X.I
  | .inr p => (G.obj (X.obj p.1)).fiber p.2

/-- The base map of the family morphism attached to a morphism of formal coproducts. -/
def expMapBase {X Y : FormalCoproduct.{w} C} (f : X ⟶ Y) : expBase G X → expBase G Y
  | .inl u => .inl u
  | .inr p => .inr ⟨f.f p.1, (G.map (f.φ p.1)).base p.2⟩

/-- The fibre maps of the family morphism attached to a morphism of formal coproducts. -/
def expMapFiber {X Y : FormalCoproduct.{w} C} (f : X ⟶ Y) :
    ∀ s, expFiber G X s → expFiber G Y (expMapBase G f s)
  | .inl _ => f.f
  | .inr p => (G.map (f.φ p.1)).fiber p.2

/-- The functor sending a formal coproduct `X` of objects of `C` to the family obtained by
joining the singleton family on `X.I` and the families `G (X.obj a)`. -/
def expFam : FormalCoproduct.{w} C ⥤ Fam.{w} where
  obj X := ⟨expBase G X, expFiber G X⟩
  map f := ⟨expMapBase G f, expMapFiber G f⟩
  map_id X := by
    refine Fam.Hom.ext' (funext fun s => ?_) (fun s x => ?_)
    · rcases s with u | ⟨a, i⟩
      · rfl
      · exact congrArg (fun j => (Sum.inr ⟨a, j⟩ : expBase G X)) (Fam.Hom.congr_base (G.map_id (X.obj a)) i)
    · rcases s with u | ⟨a, i⟩
      · rfl
      · exact Fam.Hom.congr_fiber (G.map_id (X.obj a)) i x
  map_comp f g := by
    refine Fam.Hom.ext' (funext fun s => ?_) (fun s x => ?_)
    · rcases s with u | ⟨a, i⟩
      · rfl
      · exact congrArg (fun j => (Sum.inr ⟨g.f (f.f a), j⟩ : expBase G _))
          (Fam.Hom.congr_base (G.map_comp (f.φ a) (g.φ (f.f a))) i)
    · rcases s with u | ⟨a, i⟩
      · rfl
      · exact Fam.Hom.congr_fiber (G.map_comp (f.φ a) (g.φ (f.f a))) i x

/-- The partial exponential, as an object of `ColaxSliceCart`. -/
def expObj : ColaxSliceCart.{w, w, w + 1} := ⟨Cat.of (FormalCoproduct.{w} C), expFam G⟩

/-- The projection of the partial exponential to `SetObj`. -/
def expPi : expObj G ⟶ SetObj.{w} where
  functor := idx C
  nat :=
    { app X := (⟨fun _ => .inl PUnit.unit, fun _ x => x⟩ : Fam.Hom _ ((expFam G).obj X))
      naturality _ _ _ := rfl }
  isPointwiseCartesian _ _ := ⟨rfl, fun _ => rfl⟩

/-- The counit of the partial exponential. -/
def expEps : pbObj (expPi G) ⟶ (⟨C, G⟩ : ColaxSliceCart.{w, w, w + 1}) where
  functor := eps C
  nat :=
    { app x := (⟨fun i => .inr ⟨x.2, i⟩, fun _ y => y⟩ :
        Fam.Hom (G.obj (x.1.obj x.2)) ((expFam G).obj x.1))
      naturality x y f := by
        obtain ⟨X, a⟩ := x
        obtain ⟨Y, b⟩ := y
        obtain ⟨g, hg⟩ := f
        change X ⟶ Y at g
        obtain rfl : b = g.f a := hg.symm
        refine Fam.Hom.ext' (funext fun i => ?_) (fun i z => ?_)
        · change Sum.inr _ = Sum.inr _
          simp [eps]
        · change HEq ((G.map (g.φ a ≫ eqToHom rfl)).fiber i z) ((G.map (g.φ a)).fiber i z)
          rw [eqToHom_refl, Category.comp_id] }
  isPointwiseCartesian _ _ := ⟨rfl, fun _ => rfl⟩

/-- The partial exponential data of `UFam` at `(C, G)`. -/
def expData : Data UFam.{w} (⟨C, G⟩ : ColaxSliceCart.{w, w, w + 1}) where
  P := expObj G
  pi := expPi G
  Pbk := pbChosen (expPi G)
  epsilon := expEps G

end Exp

/-! ### Universality -/

section Universal

variable {C : Cat.{w, w + 1}} {G : C ⥤ Fam.{w}} {D : ColaxSliceCart.{w, w, w + 1}}

section Mor

variable (f : D ⟶ SetObj.{w}) (g : pbObj f ⟶ (⟨C, G⟩ : ColaxSliceCart.{w, w, w + 1}))

/-- The base map of the natural transformation of `morHom f g`. -/
def morBase (x : D.cat) :
    expBase G ((morF f.functor g.functor).obj x) → (D.F.obj x).base
  | .inl _ => (f.nat.app x).base PUnit.unit
  | .inr p => (g.nat.app ⟨x, p.1⟩).base p.2

lemma morFiber_eq (x : D.cat) (s : expBase G ((morF f.functor g.functor).obj x)) :
    expFiber G _ s = (D.F.obj x).fiber (morBase f g x s) := by
  rcases s with u | ⟨a, i⟩
  · exact (f.isPointwiseCartesian x).fiber_eq PUnit.unit
  · exact (g.isPointwiseCartesian ⟨x, a⟩).fiber_eq i

/-- The components of the natural transformation of `morHom f g`. -/
def morApp (x : D.cat) :
    Fam.Hom ((expFam G).obj ((morF f.functor g.functor).obj x)) (D.F.obj x) :=
  ⟨morBase f g x, fun s y => cast (morFiber_eq f g x s) y⟩

/-- The morphism `D ⟶ expObj G` corresponding to a morphism `pbObj f ⟶ (C, G)`. -/
def morHom : D ⟶ expObj G where
  functor := morF f.functor g.functor
  nat :=
    { app := morApp f g
      naturality := fun x x' φ => by
        refine Fam.Hom.ext' (funext fun s => ?_) (fun s => ?_)
        · rcases s with u | ⟨a, i⟩
          · exact (Fam.nat_base f.nat φ PUnit.unit).symm
          · exact (Fam.nat_base g.nat (CategoryOfElements.homMk (f.functor.elementsMk x a)
              (f.functor.elementsMk x' (f.functor.map φ a)) φ rfl) i).symm
        · rcases s with u | ⟨a, i⟩
          · intro y
            refine (cast_heq _ _).trans ?_
            have hy : cast (morFiber_eq f g x (.inl u)) y = (f.nat.app x).fiber PUnit.unit y :=
              eq_of_heq ((cast_heq _ _).trans
                ((f.isPointwiseCartesian x).fiber_heq PUnit.unit y).symm)
            refine HEq.trans ?_ (heq_of_eq (congrArg _ hy)).symm
            refine HEq.trans ?_ (Fam.nat_fiber f.nat φ PUnit.unit y).symm
            exact ((f.isPointwiseCartesian x').fiber_heq _ _).symm
          · intro y
            refine (cast_heq _ _).trans ?_
            have hy : cast (morFiber_eq f g x (.inr ⟨a, i⟩)) y =
                (g.nat.app ⟨x, a⟩).fiber i y :=
              eq_of_heq ((cast_heq _ _).trans
                ((g.isPointwiseCartesian ⟨x, a⟩).fiber_heq i y).symm)
            refine HEq.trans ?_ (heq_of_eq (congrArg _ hy)).symm
            refine HEq.trans ?_ (Fam.nat_fiber g.nat (CategoryOfElements.homMk (f.functor.elementsMk x a)
              (f.functor.elementsMk x' (f.functor.map φ a)) φ rfl) i y).symm
            exact ((g.isPointwiseCartesian _).fiber_heq _ _).symm }
  isPointwiseCartesian x s := ⟨morFiber_eq f g x s, fun _ => rfl⟩

lemma morHom_isSlice : f = morHom f g ≫ expPi G :=
  Hom.ext_of_functor_eq rfl (fun _ => heq_of_eq (funext fun _ => rfl))

end Mor

section Psi

variable (k : D ⟶ expObj G) (h : D ⟶ SetObj.{w}) (e : h = k ≫ expPi G)
include e

lemma idx_eq' : k.functor ⋙ idx C = h.functor := (Hom.functor_eq_of_eq e).symm

/-- The map between pullbacks induced by `k : D ⟶ expObj G` over `SetObj`. -/
def psiHom : pbObj h ⟶ pbObj (expPi G) where
  functor := Psi k.functor (idx_eq' k h e)
  nat :=
    { app x := k.nat.app x.1
      naturality _ _ φ := k.nat.naturality φ.1 }
  isPointwiseCartesian x := k.isPointwiseCartesian x.1

lemma fbf_eq' : FBF_on_mor (expData G) (pbChosen h) e = psiHom k h e := by
  subst e
  apply (expData G).Pbk.hom_ext
  · rw [FBF_on_mor, pullbackMor1, IsPullback.lift_fst]
    exact Hom.ext_of_functor_eq (elLift_fac_left _ _ _).symm
      (fun _ => heq_of_eq (funext fun _ => rfl))
  · rw [FBF_on_mor, pullbackMor1, IsPullback.lift_snd]
    exact Hom.ext_of_functor_eq rfl (fun _ => HEq.rfl)

lemma recon' : k = morHom h (psiHom k h e ≫ expEps G) := by
  subst e
  refine Hom.ext_of_functor_eq (recon k.functor (idx_eq' k _ rfl)) (fun x => heq_of_eq ?_)
  funext s
  rcases s with u | ⟨a, i⟩ <;> rfl

end Psi

lemma morHom_comm (f : D ⟶ SetObj.{w}) (g : pbObj f ⟶ (⟨C, G⟩ : ColaxSliceCart.{w, w, w + 1})) :
    g = FBF_on_mor (expData G) (pbChosen f) (morHom_isSlice f g) ≫ expEps G := by
  rw [fbf_eq']
  exact Hom.ext_of_functor_eq (psi_eps f.functor g.functor).symm (fun _ => HEq.rfl)

variable (G) in
/-- `expData G` is universal.

[Paper, §4.1, Thm. `thm:colax-exponentiable`]: `UFam` is exponentiable. -/
@[reducible]
noncomputable def expUniversal : Universal (expData G) :=
  universal_of_chosen (expData G) (fun f => pbChosen f)
    (fun {_ f} g => morHom f g)
    (fun {_ f} g => morHom_isSlice f g)
    (fun {_ f} g => morHom_comm f g)
    (fun {_ f g h} eq_fp eq_gp H => by
      rw [fbf_eq' _ _ eq_fp, fbf_eq' _ _ eq_gp] at H
      rw [recon' f h eq_fp, recon' g h eq_gp]
      exact congrArg (morHom h) H)

end Universal

/-- The forgetful functor from pointed types, equipped with the identity natural transformation
between the singleton-base families, is an exponentiable arrow in `ColaxSliceCart`. -/
noncomputable instance isExpArr_UFam : IsExpArr UFam.{w} where
  isExpArrowData c := expData c.F
  isExpArrow c := expUniversal c.F

end ColaxSliceCartExponentiable
