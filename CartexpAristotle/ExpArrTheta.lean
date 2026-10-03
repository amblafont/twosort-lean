import CartexpAristotle.SliceFunctor
import CartexpAristotle.ExpArrCat

/-!
# The comparison `F (P X_A) ≅ P X_B` for a morphism of `ExpArrCat`
-/

open CategoryTheory Limits

universe v u

section Generic

variable {C : Type*} [Category C] {X Y : C} {u : Y ⟶ X}

lemma FBF_on_mor_comp {c c' c'' : C} (d₁ : Data u c) (d₂ : Data u c') (d₃ : Data u c'')
    {f : d₁.P ⟶ d₂.P} {g : d₂.P ⟶ d₃.P} (hf : d₁.pi = f ≫ d₂.pi) (hg : d₂.pi = g ≫ d₃.pi)
    (hfg : d₁.pi = (f ≫ g) ≫ d₃.pi) :
    FBF_on_mor d₃ d₁.Pbk hfg = FBF_on_mor d₂ d₁.Pbk hf ≫ FBF_on_mor d₃ d₂.Pbk hg := by
  apply d₃.Pbk.hom_ext
  · simp
  · simp

lemma FBF_on_mor_id {c : C} (d : Data u c) (h : d.pi = 𝟙 d.P ≫ d.pi) :
    FBF_on_mor d d.Pbk h = 𝟙 _ := by
  apply d.Pbk.hom_ext
  · simp
  · simp

lemma canonical_mor'_comp {c c' c'' : C} (g : c ⟶ c') (g' : c' ⟶ c'') (d₁ : Data u c)
    (d₂ : Data u c') [Universal d₂] (d₃ : Data u c'') [Universal d₃] :
    canonical_mor' g d₂ d₁ ≫ canonical_mor' g' d₃ d₂ = canonical_mor' (g ≫ g') d₃ d₁ := by
  have h1 : d₁.pi = canonical_mor' g d₂ d₁ ≫ d₂.pi := Universal.isSlice (d₁.epsilon ≫ g)
  have h2 : d₂.pi = canonical_mor' g' d₃ d₂ ≫ d₃.pi := Universal.isSlice (d₂.epsilon ≫ g')
  have h3 : d₁.pi = (canonical_mor' g d₂ d₁ ≫ canonical_mor' g' d₃ d₂) ≫ d₃.pi := by
    rw [Category.assoc, ← h2, ← h1]
  refine mor_unique (d1 := d₃) (d₁.epsilon ≫ g ≫ g') _ h3 ?_
  have e1 : d₁.epsilon ≫ g = FBF_on_mor d₂ d₁.Pbk h1 ≫ d₂.epsilon := Universal.comm _
  have e2 : d₂.epsilon ≫ g' = FBF_on_mor d₃ d₂.Pbk h2 ≫ d₃.epsilon := Universal.comm _
  change _ = FBF_on_mor d₃ d₁.Pbk h3 ≫ d₃.epsilon
  rw [FBF_on_mor_comp d₁ d₂ d₃ h1 h2 h3, Category.assoc, ← e2, ← Category.assoc, e1,
    Category.assoc]

lemma canonical_mor'_id {c : C} (d : Data u c) [Universal d] : canonical_mor' (𝟙 c) d d = 𝟙 _ := by
  have h : d.pi = 𝟙 d.P ≫ d.pi := (Category.id_comp _).symm
  symm
  refine mor_unique (d1 := d) (d.epsilon ≫ 𝟙 c) _ h ?_
  change _ = FBF_on_mor d d.Pbk h ≫ d.epsilon
  rw [FBF_on_mor_id, Category.id_comp, Category.comp_id]

end Generic

namespace ExpArrCat

variable {A B : ExpArrCat.{v, u}} (F : A ⟶ B)

/-- The chosen universal `Data` of the arrow of `A` at its codomain. -/
noncomputable abbrev dX (A : ExpArrCat.{v, u}) : Data A.arr A.cod := SliceExp.sX A.arr

noncomputable instance dX_univ (A : ExpArrCat.{v, u}) : Universal (dX A) :=
  IsExpArr.isExpArrow A.cod

/-- The image under `F` of `dX A`, transported along `F.iso` to an `Data` for `B.arr`. -/
noncomputable def Eθ : Data B.arr (F.functor.obj A.cod) :=
  lift_arrow_iso F.iso (functor_on F.functor (dX A))

noncomputable instance Eθ_univ : Universal (Eθ F) := by
  haveI : Universal (functor_on F.functor (dX A)) :=
    FunctorPreserves.functor_preserves (u := A.arr) (F := F.functor) (dX A) inferInstance
  exact lift_arrow_iso_univ F.iso _

/-- The comparison `F (P X_A) ⟶ P X_B`. -/
noncomputable def θ : F.functor.obj (SliceExp.sZ A.arr) ⟶ SliceExp.sZ B.arr :=
  canonical_mor' F.iso.hom.right (dX B) (Eθ F)

lemma θ_pi : θ F ≫ (dX B).pi = F.functor.map (dX A).pi ≫ F.iso.hom.right :=
  (Universal.isSlice (data := dX B) (Kuf := (Eθ F).Pbk) ((Eθ F).epsilon ≫ F.iso.hom.right)).symm

lemma θ_eps : F.functor.map (dX A).epsilon ≫ F.iso.hom.right =
    FBF_on_mor (dX B) (Eθ F).Pbk (θ_pi F).symm ≫ (dX B).epsilon :=
  Universal.comm (data := dX B) (Kuf := (Eθ F).Pbk) ((Eθ F).epsilon ≫ F.iso.hom.right)

/-- The inverse of `θ`. -/
noncomputable def θinv : SliceExp.sZ B.arr ⟶ F.functor.obj (SliceExp.sZ A.arr) :=
  canonical_mor' F.iso.inv.right (Eθ F) (dX B)

noncomputable instance θ_isIso : IsIso (θ F) :=
  ⟨θinv F,
    (canonical_mor'_comp F.iso.hom.right F.iso.inv.right (Eθ F) (dX B) (Eθ F)).trans (by
      rw [right_hom_inv F.iso]; exact canonical_mor'_id _),
    (canonical_mor'_comp F.iso.inv.right F.iso.hom.right (dX B) (Eθ F) (dX B)).trans (by
      rw [right_inv_hom F.iso]; exact canonical_mor'_id _)⟩

end ExpArrCat
