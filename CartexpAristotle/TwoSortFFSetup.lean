/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import CartexpAristotle.InitialModelUnique

/-!
# Models of two-sortified theories: setup

We follow the appendix section "Two-sortification is fully faithful". Let `A` (`FinGat`) be a
bi-initial object of `ExpArrCat` with `w`-small hom-types, and let `C₀ = Φ CatExp` be the image of
`Cat` (with `U : Pointed ⥤ Type`) under the endofunctor `Φ`: its underlying category is the slice
of `Cat` over `𝔽 = FormalCoproduct (Type w)` (families of types), its chosen codomain is the
category of elements `El` of `idx : 𝔽 ⥤ Type` (families with a chosen index), and its chosen
domain is the pullback `PB` of `U` along the evaluation `El ⥤ Type`.

For a morphism `G : A ⟶ C₀` (in the application, the two-sortification functor followed by `Φ`
of the model functor, which is the functor `Γ ↦ Mod (T Γ)` of the appendix up to the
isomorphism of Uemura's theorem), we set up:

* `gX : G X ⥤ Type`: the sort of a model of `X` (the fibre of its family at its index);
* `gY : G Y ⥤ Pointed`: the sort of a model of `Y` with its distinguished term;
* `gIsPullback`: these form a pullback square over `G p` and `U`, giving a concrete criterion
  (`critG`).
-/

open CategoryTheory Limits

universe w

namespace ExpArrCat

namespace TwoSortFF

open FamOverExpArr PointedForget SliceExp

noncomputable section

/-- `Φ CatExp`: the slice of `Cat` over families of types, with the arrow `p'`. -/
abbrev C₀ : ExpArrCat.{w + 1, w + 2} := Φobj.{w + 1, w + 2} CatExp.{w}

/-- Families of types, as formal coproducts of types. -/
abbrev 𝔽 : Cat.{w, w + 1} := sZ U.{w}

/-- Families of types with a chosen index. -/
abbrev El : Cat.{w, w + 1} := (sX U.{w}).Pbk.pullback

/-- The chosen domain of `C₀`. -/
abbrev PB : Cat.{w, w + 1} := sY' U.{w}

section Setup

variable {A : ExpArrCat.{w + 1, w + 2}} (G : A ⟶ C₀.{w})

/-- The underlying category of `G Γ`. -/
abbrev GL (Γ : A.carrier) : Cat.{w, w + 1} := (G.functor.obj Γ).left

/-- The family of a model. -/
abbrev famF (Γ : A.carrier) : GL G Γ ⥤ FormalCoproduct.{w} (Type w) :=
  (G.functor.obj Γ).hom.toFunctor

/-- The underlying functor of `G σ`. -/
abbrev Gm {Γ Γ' : A.carrier} (σ : Γ ⟶ Γ') : GL G Γ ⥤ GL G Γ' := (G.functor.map σ).left.toFunctor

/-- The identification of `G X` with families with an index. -/
abbrev isoX : GL G A.cod ⥤ (idx (Type w)).Elements := G.iso.hom.right.left.toFunctor

/-- The identification of `G Y` with `PB`. -/
abbrev isoY : GL G A.dom ⥤ PB.{w} := G.iso.hom.left.left.toFunctor

/-- The sort of a model of `X`, as a morphism of `Cat`. -/
def gXhom : GL G A.cod ⟶ Cat.of (Type w) := G.iso.hom.right.left ≫ sE U.{w}

/-- The pointed sort of a model of `Y`, as a morphism of `Cat`. -/
def gYhom : GL G A.dom ⟶ Cat.of Pointed.{w} := G.iso.hom.left.left ≫ pullback.fst U.{w} (sE U.{w})

/-- The sort of a model of `X`. -/
abbrev gX : GL G A.cod ⥤ Type w := (gXhom G).toFunctor

/-- The pointed sort of a model of `Y`. -/
abbrev gY : GL G A.dom ⥤ Pointed.{w} := (gYhom G).toFunctor

lemma isoY_su' : G.iso.hom.left.left ≫ su' U.{w} = (G.functor.map A.arr).left ≫ G.iso.hom.right.left :=
  congrArg CommaMorphism.left G.iso.hom.w

lemma isoX_hom : G.iso.hom.right.left ≫ sW U.{w} = (G.functor.obj A.cod).hom :=
  Over.w G.iso.hom.right

lemma isoY_hom : G.iso.hom.left.left ≫ su' U.{w} ≫ sW U.{w} = (G.functor.obj A.dom).hom :=
  Over.w G.iso.hom.left

lemma gsq : gYhom G ≫ U.{w} = (G.functor.map A.arr).left ≫ gXhom G := by
  simp only [gYhom, gXhom, Category.assoc, pullback.condition]
  rw [← Category.assoc, isoY_su', Category.assoc]

instance : IsIso G.iso.hom.left.left := by
  have : IsIso G.iso.hom.left := inferInstance
  exact inferInstanceAs (IsIso ((Over.forget _).map G.iso.hom.left))

instance : IsIso G.iso.hom.right.left := by
  have : IsIso G.iso.hom.right := inferInstance
  exact inferInstanceAs (IsIso ((Over.forget _).map G.iso.hom.right))

lemma gIsPullback : IsPullback (gYhom G) (G.functor.map A.arr).left U.{w} (gXhom G) := by
  have h₁ : IsPullback G.iso.hom.left.left (G.functor.map A.arr).left (su' U.{w})
      G.iso.hom.right.left := IsPullback.of_horiz_isIso ⟨isoY_su' G⟩
  exact h₁.paste_horiz (shpb U.{w})

lemma gw : gY G ⋙ forget Pointed = Gm G A.arr ⋙ gX G :=
  congrArg Cat.Hom.toFunctor (gsq G)

/-- The distinguished element of `gX (G p e)` for `e : G Y`. -/
def mptG (e : GL G A.dom) : (gX G).obj ((Gm G A.arr).obj e) :=
  elPt (gY G) (Gm G A.arr) (gw G) e

lemma mptG_map {e e' : GL G A.dom} (u : e ⟶ e') :
    (gX G).map ((Gm G A.arr).map u) (mptG G e) = mptG G e' :=
  elPt_map _ _ _ u

lemma gY_eq : gY G = pointify (Gm G A.arr ⋙ gX G) (mptG G) (fun f => mptG_map G f) := by
  refine CategoryTheory.Functor.hext (fun e => (pointed_mk_cast _ _ _).symm) fun e e' u => ?_
  refine pointed_hom_heq (pointed_mk_cast _ _ _).symm (pointed_mk_cast _ _ _).symm _ _ ?_
  intro x x' hx
  exact heq_map (gw G) u x x' hx

lemma critG : PointifyCrit (G.functor.map A.arr).left (gXhom G) (mptG G) := by
  refine pointifyCrit_of_isPullback _ _ _ (fun f => mptG_map G f) ?_
  have : pointifyHom (G.functor.map A.arr).left (gXhom G) (mptG G) (fun f => mptG_map G f) =
      gYhom G := Cat.Hom.ext (gY_eq G).symm
  rw [this]
  exact gIsPullback G

end Setup

end

end TwoSortFF

end ExpArrCat
