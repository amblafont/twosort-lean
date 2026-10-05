/-
Copyright (c) 2026 Lean Contributor. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Contributor
-/
import CartexpAristotle.InfiniteGat.ProExtendExp
import CartexpAristotle.InfiniteGat.Limits
import CartexpAristotle.CompExp.UniversalNatTrans
import CartexpAristotle.AdjointExp

/-!
# Infinite GATs: bi-initiality of the pro-completion of `FinGat`

Let `FinGat` be a bi-initial object of `Lexp` whose underlying category is essentially small
(the category of finite GATs). The category `GatCat` of (possibly infinite) GATs is the
pro-completion `Pro FinGat` of `FinGat` (more precisely, of a small model of it), equipped with
the image of the chosen exponentiable arrow `pGAT` under the embedding `iGAT : FinGat ⥤ GatCat`.

**Main theorem** (`InfiniteGat.gatCat_isBiInitial`, [Paper, App., Thm. `thm:infinite-GATs`]):
`GatCat` is bi-initial in the 2-category `CompExp` of complete categories (with a terminal
object and all small wide pullbacks, equivalently all small limits) equipped with an exponentiable
arrow, whose morphisms are the functors preserving small limits and pushforwards along the
exponentiable arrow, equipped with an isomorphism between the image of the chosen arrow and the
chosen arrow of the target.

The morphisms of `CompExp` are exactly the limit-preserving functors (preserving the exponentiable
arrow): see `InfiniteGat.preservesLimitsOfSize_of_preservesWidePullbacks`.

## Proof

* existence: a morphism `G : FinGat ⟶ B` of `Lexp` extends to a limit-preserving functor
  `proExtend G : GatCat ⥤ B` (right Kan extension), which preserves pushforwards along `iGAT pGAT`
  (`proExtend_functorPreserves`);
* uniqueness: natural transformations between limit-preserving functors `GatCat ⥤ B` correspond
  to natural transformations between their restrictions along `iGAT` (`proRestrictEquiv`), and
  these are unique by bi-initiality of `FinGat`.
-/

open CategoryTheory Limits Functor

universe w

namespace InfiniteGat

section EquivPUnit

variable {T : Type*} [Category T]

/-- A category with an object, in which every hom-set is a singleton, is equivalent to the
terminal category. -/
noncomputable def equivPUnitOfUnique (t : T) (hne : ∀ a b : T, Nonempty (a ⟶ b))
    (hs : ∀ a b : T, Subsingleton (a ⟶ b)) : T ≌ Discrete PUnit.{1} :=
  CategoryTheory.Equivalence.mk (Functor.star T) ((Functor.const _).obj t)
    (NatIso.ofComponents (fun a => ⟨(hne a t).some, (hne t a).some, (hs _ _).elim _ _,
      (hs _ _).elim _ _⟩) (fun _ => (hs _ _).elim _ _))
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => Subsingleton.elim _ _))

end EquivPUnit

variable (FinGat : Lexp.{w, w + 1}) [EssentiallySmall.{w} FinGat.carrier]

/-- A small model of `FinGat`. -/
abbrev FinGat₀ : Type w := SmallModel.{w} FinGat.carrier

/-- The equivalence between `FinGat` and its small model. -/
noncomputable abbrev finGatEquiv : FinGat.carrier ≌ FinGat₀ FinGat := equivSmallModel _

instance : HasPullbacks (FinGat₀ FinGat) :=
  Adjunction.hasLimitsOfShape_of_equivalence (finGatEquiv FinGat).inverse

instance : HasTerminal (FinGat₀ FinGat) :=
  Adjunction.hasLimitsOfShape_of_equivalence (finGatEquiv FinGat).inverse

instance : HasFiniteLimits (FinGat₀ FinGat) := hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- The chosen arrow of `FinGat`, in the small model. -/
noncomputable abbrev arr₀ := (finGatEquiv FinGat).functor.map FinGat.arr

noncomputable instance : IsExpArr (arr₀ FinGat) :=
  IsExpArr.ofEquivalence (finGatEquiv FinGat).symm FinGat.arr

/-- **The category of GATs**: the pro-completion of (a small model of) `FinGat`, with the image of
the chosen arrow `pGAT` of `FinGat`, as an object of `CompExp`. -/
noncomputable abbrev GatCat : CompExp.{w, w, w + 1} :=
  CompExp.of (Pro (FinGat₀ FinGat)) ((proYoneda (FinGat₀ FinGat)).map (arr₀ FinGat))

/-- The embedding `iGAT : FinGat ⥤ GatCat`. -/
noncomputable abbrev iGatFunctor : FinGat.carrier ⥤ Pro (FinGat₀ FinGat) :=
  (finGatEquiv FinGat).functor ⋙ proYoneda (FinGat₀ FinGat)

noncomputable instance : FunctorPreserves FinGat.arr (finGatEquiv FinGat).functor :=
  functorPreserves_of_adjunction (frobenius_equivalence (finGatEquiv FinGat).symm FinGat.arr)

/-- The embedding `iGAT : FinGat ⟶ GatCat`, as a morphism of `Lexp`. -/
noncomputable def iGat : FinGat ⟶ (GatCat FinGat).toLexp where
  functor := iGatFunctor FinGat
  iso := Iso.refl _

lemma iGat_functor : (iGat FinGat).functor = iGatFunctor FinGat := rfl

lemma iGat_iso : (iGat FinGat).iso = Iso.refl _ := rfl

variable {FinGat}

section Existence

variable {B : CompExp.{w, w, w + 1}} (G : FinGat ⟶ B.toLexp)

/-- The restriction of `G` to the small model of `FinGat`. -/
noncomputable abbrev smallFunctor : FinGat₀ FinGat ⥤ B.carrier :=
  (finGatEquiv FinGat).inverse ⋙ G.functor

instance : PreservesFiniteLimits G.functor :=
  preservesFiniteLimits_of_preservesTerminal_and_pullbacks _

instance : PreservesFiniteLimits (smallFunctor G) := by
  unfold smallFunctor; infer_instance

/-- `e⁻¹ (e pGAT) ≅ pGAT`. -/
noncomputable def arr₀Iso :
    Arrow.mk ((finGatEquiv FinGat).inverse.map (arr₀ FinGat)) ≅ Arrow.mk FinGat.arr :=
  Arrow.isoMk ((finGatEquiv FinGat).unitIso.app _).symm ((finGatEquiv FinGat).unitIso.app _).symm
    (by simp)

noncomputable instance : FunctorPreserves (arr₀ FinGat) (finGatEquiv FinGat).inverse :=
  functorPreserves_of_adjunction (frobenius_equivalence (finGatEquiv FinGat) (arr₀ FinGat))

noncomputable instance :
    FunctorPreserves ((finGatEquiv FinGat).inverse.map (arr₀ FinGat)) G.functor :=
  functor_preserves_iso FinGat.arr _ G.functor (arr₀Iso (FinGat := FinGat))

noncomputable instance : FunctorPreserves (arr₀ FinGat) (smallFunctor G) :=
  functor_preserves_comp _ _ _

/-- The isomorphism between the image of the chosen arrow of `GatCat` under the extension of `G`
and the chosen arrow of `B`. -/
noncomputable def extendIso :
    Arrow.mk ((proExtend (smallFunctor G)).map ((proYoneda (FinGat₀ FinGat)).map (arr₀ FinGat))) ≅
      Arrow.mk B.arr :=
  Arrow.isoMk ((proExtendIso (smallFunctor G)).app _) ((proExtendIso (smallFunctor G)).app _)
      ((proExtendIso (smallFunctor G)).hom.naturality _).symm ≪≫
    G.functor.mapArrow.mapIso (arr₀Iso (FinGat := FinGat)) ≪≫ G.iso

/-- **The extension of a morphism `G : FinGat ⟶ B` of `Lexp` to a morphism `GatCat ⟶ B` of
`CompExp`.** -/
noncomputable def extendHom : GatCat FinGat ⟶ B :=
  CompExp.Hom.mk' (proExtend (smallFunctor G)) (proExtend_functorPreserves _ _) (extendIso G)

end Existence

section Uniqueness

variable {B : CompExp.{w, w, w + 1}}

instance (H : CompExp.Hom (GatCat FinGat) B) : PreservesLimitsOfSize.{w, w} H.functor :=
  haveI := H.toHom.preservesTerminal
  haveI : ∀ J : Type w, PreservesLimitsOfShape (WidePullbackShape J) H.functor :=
    H.preservesWidePullbacks
  preservesLimitsOfSize_of_preservesWidePullbacks.{w} H.functor

/-- Whiskering along the equivalence `FinGat ≌ FinGat₀`. -/
noncomputable abbrev whiskerE : (FinGat₀ FinGat ⥤ B.carrier) ⥤ (FinGat.carrier ⥤ B.carrier) :=
  (whiskeringLeft _ _ _).obj (finGatEquiv FinGat).functor

/-- 2-cells `H ⟶ K` out of `GatCat` are determined by their restriction along `iGAT`. -/
lemma hom₂_ext_of_restrict {H K : GatCat FinGat ⟶ B} (α β : H ⟶ K)
    (h : (Lexp.Hom₂.whiskerLeft (iGat FinGat) α).nat =
      (Lexp.Hom₂.whiskerLeft (iGat FinGat) β).nat) : α = β := by
  apply Lexp.Hom₂.ext
  apply (proRestrictEquiv H.functor K.functor).injective
  rw [proRestrictEquiv_apply, proRestrictEquiv_apply]
  exact (whiskerE (FinGat := FinGat) (B := B)).map_injective h

variable (hFin : Lexp.IsBiInitial FinGat)
include hFin

lemma hom₂_subsingleton (H K : GatCat FinGat ⟶ B) : Subsingleton (H ⟶ K) :=
  ⟨fun α β => hom₂_ext_of_restrict α β
    (congrArg Lexp.Hom₂.nat (hFin.hom₂_ext (Lexp.Hom₂.whiskerLeft (iGat FinGat) α)
      (Lexp.Hom₂.whiskerLeft (iGat FinGat) β)))⟩

lemma hom₂_nonempty (H K : GatCat FinGat ⟶ B) : Nonempty (H ⟶ K) := by
  let γ : iGat FinGat ≫ H.toLexpHom ⟶ iGat FinGat ≫ K.toLexpHom :=
    (hFin.nonempty_iso _ _).some.hom
  let γ' : (whiskerE (FinGat := FinGat) (B := B)).obj (proYoneda _ ⋙ H.functor) ⟶
      (whiskerE (FinGat := FinGat) (B := B)).obj (proYoneda _ ⋙ K.functor) := γ.nat
  let δ : proYoneda _ ⋙ H.functor ⟶ proYoneda _ ⋙ K.functor :=
    (whiskerE (FinGat := FinGat) (B := B)).preimage γ'
  let α : H.functor ⟶ K.functor := (proRestrictEquiv H.functor K.functor).symm δ
  have h1 : whiskerLeft (proYoneda _) α = δ := by
    rw [← proRestrictEquiv_apply, Equiv.apply_symm_apply]
  have h2 : ∀ d, α.app ((proYoneda _).obj ((finGatEquiv FinGat).functor.obj d)) = γ.nat.app d :=
    fun d => by
    have := congrArg (fun t => NatTrans.app t ((finGatEquiv FinGat).functor.obj d)) h1
    refine this.trans ?_
    exact congrArg (fun t => NatTrans.app t d) ((whiskerE (FinGat := FinGat) (B := B)).map_preimage γ')
  refine ⟨(⟨α, ?_, ?_⟩ : Lexp.Hom₂ H.toLexpHom K.toLexpHom)⟩
  · have := γ.left_comm
    simp only [Lexp.Hom.comp_iso_hom_left, iGat_iso] at this
    rw [h2]; simpa using this
  · have := γ.right_comm
    simp only [Lexp.Hom.comp_iso_hom_right, iGat_iso] at this
    rw [h2]; simpa using this

end Uniqueness

/-- **Infinite GATs** ([Paper, App., Thm. `thm:infinite-GATs`]). Let `FinGat` be a bi-initial
object of `Lexp` (the category of finite GATs with `pGAT`) whose underlying category is essentially
small. Then the category of GATs `GatCat`, the pro-completion of `FinGat`, equipped with `iGAT pGAT`,
is bi-initial in the 2-category `CompExp` of complete categories with an exponentiable arrow and
limit-preserving functors preserving pushforwards along it. -/
theorem gatCat_isBiInitial (hFin : Lexp.IsBiInitial FinGat) : CompExp.IsBiInitial (GatCat FinGat) :=
  fun B => ⟨equivPUnitOfUnique (extendHom (hFin.nonempty_hom B.toLexp).some)
    (hom₂_nonempty hFin) (hom₂_subsingleton hFin)⟩

end InfiniteGat
