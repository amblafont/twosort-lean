import CartexpAristotle.ColaxSliceCartForget
import CartexpAristotle.TwoSortification

/-!
# The family functor of a GAT

Let `FinGat` be a bi-initial object of `Lexp` and `M = modelFunctor` the model functor.
Following Corollary "family-functor-gat" of the paper, we construct a bi-initial morphism
`famFunctor : FinGat ⟶ ColaxSliceCartLexp` into the cartesian colax slice over `Fam` whose composite with
the projection `ColaxSliceCartLexp ⟶ CatLexp` is *equal* to the model functor (`famFunctor_comp_forget`).
Hence for every GAT `Γ`, `famFunctor Γ` is the category of models `M Γ` equipped with a functor
`familyFunctor Γ : M Γ ⥤ Fam`, the **family functor** of `Γ`.

The construction starts from any morphism `F₀ : FinGat ⟶ ColaxSliceCartLexp` and the invertible 2-cell
`F₀ ≫ forgetHom ≅ M` given by bi-initiality, and transports `F₀` along it, using that the
projection `ColaxSliceCart ⥤ Cat` is an isofibration (`ColaxSliceCart.transportIso`).

## References

* [Paper, §4.1, Cor. `cor:family-functor-gat`]: `famFunctor` is the strict bi-initial
  `Lexp`-functor `F : FinGat → CAT //_c Fam`, `famFunctor_comp_forget` says that its composite with
  the projection to `CAT` is the model functor on the nose, and `familyFunctor Γ` is the
  *family functor* `F_Γ : Mod(Γ) → Fam` of `Γ`.
-/

universe w v u

open CategoryTheory Limits ColaxSliceCart SemanticTwoSortFunctor ColaxSliceCartForget

namespace Lexp

section OfNatIso

variable {A B : Lexp.{v, u}} (F : A ⟶ B) {G : A.carrier ⥤ B.carrier} (e : F.functor ≅ G)

/-- A morphism of `Lexp` with underlying functor `G`, obtained from a morphism `F` and a
natural isomorphism `F.functor ≅ G`. -/
noncomputable def Hom.ofNatIso : A ⟶ B :=
  letI : PreservesLimitsOfShape WalkingCospan G := preservesLimitsOfShape_of_natIso e
  letI : PreservesLimitsOfShape (Discrete PEmpty.{1}) G := preservesLimitsOfShape_of_natIso e
  letI : FunctorPreserves A.arr G := functorPreserves_of_natIso _ _ e
  { functor := G
    iso := (Arrow.isoMk (e.app A.dom) (e.app A.cod) (by simp)).symm ≪≫ F.iso }

@[simp] lemma Hom.ofNatIso_functor : (Hom.ofNatIso F e).functor = G := rfl

lemma Hom.ofNatIso_iso_hom_left :
    (Hom.ofNatIso F e).iso.hom.left = e.inv.app A.dom ≫ F.iso.hom.left := rfl

lemma Hom.ofNatIso_iso_hom_right :
    (Hom.ofNatIso F e).iso.hom.right = e.inv.app A.cod ≫ F.iso.hom.right := rfl

/-- The invertible 2-cell `F ≅ Hom.ofNatIso F e`. -/
noncomputable def Hom.ofNatIsoIso : F ≅ Hom.ofNatIso F e :=
  Hom.isoMk e (by simp [Hom.ofNatIso_iso_hom_left]) (by simp [Hom.ofNatIso_iso_hom_right])

end OfNatIso

section FamilyFunctor

variable {FinGat : Lexp.{w + 1, w + 2}} (hFinGat : IsBiInitial FinGat)

/-- The chosen strict morphism from `FinGat` to the cartesian colax slice. -/
noncomputable abbrev famFunctor₀ : FinGat ⟶ ColaxSliceCartLexp.{w} := hFinGat.strictHom ColaxSliceCartLexp

/-- The invertible 2-cell `famFunctor₀ ≫ forgetHom ≅ M` given by bi-initiality. -/
noncomputable def famFunctor₀Iso : famFunctor₀ hFinGat ≫ forgetHom ≅ modelFunctor hFinGat :=
  (hFinGat.nonempty_iso _ _).some

/-- The natural isomorphism underlying `famFunctor₀Iso`. -/
noncomputable def famFunctor₀NatIso :
    (famFunctor₀ hFinGat).functor ⋙ ColaxSliceCart.forget ≅ (modelFunctor hFinGat).functor where
  hom := (famFunctor₀Iso hFinGat).hom.nat
  inv := (famFunctor₀Iso hFinGat).inv.nat
  hom_inv_id := congrArg Hom₂.nat (famFunctor₀Iso hFinGat).hom_inv_id
  inv_hom_id := congrArg Hom₂.nat (famFunctor₀Iso hFinGat).inv_hom_id

/-- The object part of `famFunctor`: `F₀(Γ)` transported to `M Γ`. -/
noncomputable def famFunctorObj (Γ : FinGat.carrier) : ColaxSliceCart.{w, w, w + 1} :=
  transportObj ((famFunctor₀ hFinGat).functor.obj Γ) ((famFunctor₀NatIso hFinGat).app Γ)

/-- The isomorphism `F₀(Γ) ≅ famFunctorObj Γ`. -/
noncomputable def famFunctorObjIso (Γ : FinGat.carrier) :
    (famFunctor₀ hFinGat).functor.obj Γ ≅ famFunctorObj hFinGat Γ :=
  transportIso _ ((famFunctor₀NatIso hFinGat).app Γ)

/-- The underlying functor of `famFunctor`. -/
noncomputable def famFunctorFun : FinGat.carrier ⥤ ColaxSliceCart.{w, w, w + 1} :=
  (famFunctor₀ hFinGat).functor.copyObj (famFunctorObj hFinGat) (famFunctorObjIso hFinGat)

/-- **The family functor** `FinGat ⟶ ColaxSliceCartLexp`: the bi-initial morphism to the cartesian
colax slice over `Fam` that lies over the model functor on the nose.

[Paper, §4.1, Cor. `cor:family-functor-gat`]: the strict bi-initial `Lexp`-functor `F : FinGat → CAT //_c Fam`. -/
noncomputable def famFunctor : FinGat ⟶ ColaxSliceCartLexp.{w} :=
  Hom.ofNatIso (famFunctor₀ hFinGat)
    ((famFunctor₀ hFinGat).functor.isoCopyObj (famFunctorObj hFinGat) (famFunctorObjIso hFinGat))

/-- The category of models of a GAT `Γ`: its image under the model functor. -/
noncomputable abbrev modelCat (Γ : FinGat.carrier) : Cat.{w, w + 1} :=
  (modelFunctor hFinGat).functor.obj Γ

lemma famFunctor_functor : (famFunctor hFinGat).functor = famFunctorFun hFinGat := rfl

/-- **The family functor of a GAT `Γ`**: a functor from the category of models of `Γ` to the
category `Fam` of families of types.

[Paper, §4.1, Cor. `cor:family-functor-gat`]: the family functor `F_Γ`. -/
noncomputable def familyFunctor (Γ : FinGat.carrier) : modelCat hFinGat Γ ⥤ Fam.{w} :=
  ((famFunctor hFinGat).functor.obj Γ).F

lemma famFunctor_obj (Γ : FinGat.carrier) :
    (famFunctor hFinGat).functor.obj Γ = ⟨modelCat hFinGat Γ, familyFunctor hFinGat Γ⟩ :=
  rfl

lemma famFunctorFun_forget :
    famFunctorFun hFinGat ⋙ ColaxSliceCart.forget = (modelFunctor hFinGat).functor := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun Γ Γ' σ => ?_)
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change ((famFunctor₀NatIso hFinGat).app Γ).inv ≫
      ColaxSliceCart.forget.map ((famFunctor₀ hFinGat).functor.map σ) ≫
      ((famFunctor₀NatIso hFinGat).app Γ').hom = _
  exact NatIso.naturality_1 (famFunctor₀NatIso hFinGat) σ

/-- The family functor lies over the model functor: its composite with the projection from the
cartesian colax slice to `Cat` is the model functor.

[Paper, §4.1, Cor. `cor:family-functor-gat`] and its proof. -/
theorem famFunctor_comp_forget : famFunctor hFinGat ≫ forgetHom = modelFunctor hFinGat := by
  refine Hom.ext' (famFunctorFun_forget hFinGat) ?_ ?_
  · have h := (famFunctor₀Iso hFinGat).inv.left_comm
    simp only [Hom.comp_iso_hom_left, forgetHom_iso_hom_left] at h ⊢
    rw [eqToHom_refl, Category.id_comp, ← h]
    rfl
  · have h := (famFunctor₀Iso hFinGat).inv.right_comm
    simp only [Hom.comp_iso_hom_right, forgetHom_iso_hom_right] at h ⊢
    rw [eqToHom_refl, Category.id_comp, ← h]
    rfl

/-- The family functor is isomorphic to any morphism `FinGat ⟶ ColaxSliceCartLexp`. -/
theorem nonempty_iso_famFunctor (F : FinGat ⟶ ColaxSliceCartLexp.{w}) :
    Nonempty (F ≅ famFunctor hFinGat) :=
  hFinGat.nonempty_iso _ _

end FamilyFunctor

end Lexp
