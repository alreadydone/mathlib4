/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Sheaves.LocalPredicate

/-!
# Étale spaces of local predicates and presheaves

This file establishes the connection between `TopCat.LocalPredicate` on a family of types
over a base space `B` (think of a set of sections over `B`) and local homeomorphisms to `B`
(i.e., étale spaces over `B`).

In the file `Mathlib.Topology.Sheaves.Sheafify`, the connection between `TopCat.LocalPredicate`
and (pre)sheaves has been established. It combines with this file to establish the connection
between sheaves and étale spaces.

## Main definitions


-/

open CategoryTheory TopologicalSpace Opposite Set

universe u v

namespace TopCat

variable {B : TopCat.{u}} {F : B → Type v}

set_option linter.unusedVariables false in
/-- The underlying type of the étale space associated to a predicate on sections of a type family
is simply the sigma type. -/
def EtaleSpace (pred : Π ⦃U : Opens B⦄, ((Π b : U, F b) → Prop)) : Type _ := Σ b, F b

namespace EtaleSpace

variable {pred : Π ⦃U : Opens B⦄, ((Π b : U, F b) → Prop)}

/-- Constructor for points in the étale space. -/
@[simps] def mk {b : B} (x : F b) : EtaleSpace pred := ⟨b, x⟩

/-- The étale space is endowed with the strongest topology making every section continuous. -/
instance : TopologicalSpace (EtaleSpace pred) :=
  ⨆ (U : Opens B) (s : Π b : U, F b) (_ : pred s), coinduced (mk <| s ·) inferInstance

lemma isOpen_iff {V : Set (EtaleSpace pred)} :
    IsOpen V ↔
    ∀ (U : Opens B) (s : Π b : U, F b), pred s → IsOpen ((mk <| s ·) ⁻¹' V) := by
  simp_rw [isOpen_iSup_iff, isOpen_coinduced]

lemma continuous_dom_iff {X} [TopologicalSpace X] {f : EtaleSpace pred → X} :
    Continuous f ↔
    ∀ (U : Opens B) (s : Π b : U, F b), pred s → Continuous (f <| mk <| s ·) := by
  simp_rw [continuous_def, isOpen_iff, preimage_preimage,
    ← forall_comm (α := Set X), ← forall_comm (α := IsOpen _)]

variable (pred) in
/-- The projection from the étale space down to the base is continuous. -/
def proj : C(EtaleSpace pred, B) where
  toFun := Sigma.fst
  continuous_toFun := continuous_dom_iff.mpr fun _ _ _ ↦ continuous_subtype_val

section Section

variable {U : Opens B} {s : Π b : U, F b} (hs : pred s)
include hs

lemma continuous_section : Continuous fun b ↦ (mk (s b) : EtaleSpace pred) :=
  continuous_iff_coinduced_le.mpr (le_iSup₂_of_le U s <| le_iSup_of_le hs le_rfl)

/-- The domain of any section is homeomorphic to its range. -/
def homeomorphRangeSection : U ≃ₜ range fun b ↦ (mk (s b) : EtaleSpace pred) where
  toFun b := ⟨_, b, rfl⟩
  invFun x := ⟨proj pred x, by obtain ⟨_, b, rfl⟩ := x; exact b.2⟩
  left_inv _ := rfl
  right_inv := by rintro ⟨_, _, rfl⟩; rfl
  continuous_toFun := (continuous_section hs).subtype_mk _
  continuous_invFun := ((proj pred).continuous.comp continuous_subtype_val).subtype_mk <| by
    rintro ⟨_, b, rfl⟩; exact b.2

theorem isOpen_range_section (inj : ∀ b, IsStalkInj pred b) :
    IsOpen (range fun b ↦ (mk (s b) : EtaleSpace pred)) :=
  isOpen_iff.mpr fun V t ht ↦ isOpen_iff_mem_nhds.mpr fun ⟨v, hv⟩ ⟨⟨u, hu⟩, he⟩ ↦ by
    cases congr($he.1)
    have ⟨W, iU, iV, eq⟩ := inj v ⟨U, hu⟩ ⟨V, hv⟩ _ _ hs ht congr($he.2)
    exact Filter.mem_of_superset ((W.1.2.preimage continuous_subtype_val).mem_nhds W.2)
      fun v hv ↦ ⟨⟨v, iU.le hv⟩, congr(mk $(eq ⟨v, hv⟩))⟩

open Topology

theorem isOpenEmbedding_section (inj : ∀ b, IsStalkInj pred b) :
    IsOpenEmbedding fun b ↦ (mk (s b) : EtaleSpace pred) := by
  rw [isOpenEmbedding_iff, isEmbedding_iff, and_assoc]
  exact ⟨.of_comp (continuous_section hs) (proj pred).continuous .subtypeVal,
    fun _ _ eq ↦ Subtype.ext congr(proj pred $eq), isOpen_range_section hs inj⟩

theorem isOpenEmbedding_restrict_proj :
    IsOpenEmbedding ((range (mk <| s ·)).restrict (proj pred)) :=
  U.2.isOpenEmbedding_subtypeVal.comp (homeomorphRangeSection hs).symm.isOpenEmbedding

omit hs

theorem isTopologicalBasis {P : PrelocalPredicate F}
    (inj : ∀ b, IsStalkInj P.pred b) (surj : ∀ b, IsStalkSurj P.pred b) :
    IsTopologicalBasis {V : Set (EtaleSpace P.pred) |
      ∃ (U : Opens B) (s : Π b : U, F b), P.pred s ∧ V = range (mk <| s ·)} :=
  isTopologicalBasis_of_isOpen_of_nhds
      (by rintro _ ⟨U, s, hs, rfl⟩; exact isOpen_range_section hs inj) fun ⟨b, x⟩ V hx hV ↦ by
    have ⟨U, s, hs, eq⟩ := surj _ x
    let W : Opens B := ⟨_, U.1.2.isOpenMap_subtype_val _ (isOpen_iff.mp hV _ s hs)⟩
    refine ⟨_, ⟨W, _, P.res image_val_subset.hom s hs, rfl⟩,
      ⟨⟨b, ⟨b, U.2⟩, by rwa [mem_preimage, eq], rfl⟩, congr(mk $eq)⟩, ?_⟩
    rintro _ ⟨⟨_, b, hb, rfl⟩, rfl⟩
    exact hb

theorem continuous_cod_iff (inj : ∀ b, IsStalkInj pred b) (surj : ∀ b, IsStalkSurj pred b)
    {X} [TopologicalSpace X] {f : X → EtaleSpace pred} :
    Continuous f ↔ Continuous (proj pred ∘ f) ∧ ∀ x, ∃ (U : OpenNhds (f x).1) (s : Π b : U.1, F b),
      pred s ∧ ∃ V ∈ 𝓝 x, ∀ x' (h' : (f x').1 ∈ U.1), x' ∈ V → s ⟨_, h'⟩ = (f x').2 := by
  refine ⟨fun h ↦ ⟨(proj pred).continuous.comp h, fun x ↦ ?_⟩,
    fun ⟨cont, eq⟩ ↦ continuous_iff_continuousAt.mpr fun x ↦ ?_⟩
  · have ⟨U, s, hs, eq⟩ := surj _ (f x).2
    refine ⟨U, s, hs, _, ((isOpen_range_section hs inj).preimage h).mem_nhds <|
      by exact ⟨_, congr(mk $eq)⟩, fun x hx ⟨b, eq⟩ ↦ ?_⟩
    set y := f x with hy; clear_value y
    have : s ⟨y.1, hx⟩ = y.2 := by cases eq; rfl
    cases hy; exact this
  · have ⟨U, s, hs, V, hV, eq⟩ := eq x
    exact (continuousOn_iff_continuous_restrict.mpr <| ((continuous_section hs).comp
      (f := (⟨_, ·.2.1⟩)) <| (cont.comp continuous_subtype_val).subtype_mk _).congr
        fun x ↦ by exact congr(mk $(eq x x.2.1 x.2.2))).continuousAt
      (Filter.inter_mem (cont.continuousAt.preimage_mem_nhds (U.1.2.mem_nhds U.2)) hV)

theorem continuous_section_iff {P : PrelocalPredicate F}
    (inj : ∀ b, IsStalkInj P.pred b) (surj : ∀ b, IsStalkSurj P.pred b) :
    Continuous (fun b ↦ (mk (s b) : EtaleSpace P.pred)) ↔ P.sheafify.pred s := by
  rw [continuous_cod_iff inj surj, and_iff_right (by exact continuous_subtype_val)]
  constructor <;> intro h x
  · have ⟨W, t, ht, V, hV, eq⟩ := h x
    have ⟨V', hV', hV, hxV⟩ := mem_nhds_iff.mp hV
    refine ⟨W.1 ⊓ ⟨_, U.2.isOpenMap_subtype_val _ hV⟩,
      ⟨W.2, _, hxV, rfl⟩, Opens.infLERight .. ≫ image_val_subset.hom, ?_⟩
    convert ← P.res (Opens.infLELeft ..) _ ht with ⟨_, hW, x, hxV, rfl⟩
    exact eq _ _ (hV' hxV)
  · have ⟨V, hV, i, hs⟩ := h x
    exact ⟨⟨V, hV⟩, _, hs, _, (V.2.preimage continuous_subtype_val).mem_nhds hV, fun _ _ _ ↦ rfl⟩

end Section

theorem isLocalHomeomorph_proj (inj : ∀ b, IsStalkInj pred b) (surj : ∀ b, IsStalkSurj pred b) :
    IsLocalHomeomorph (proj pred) :=
  isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr fun x ↦
    have ⟨_U, _s, hs, eq⟩ := surj _ x.2
    ⟨_, (isOpen_range_section hs inj).mem_nhds ⟨_, congr(mk $eq)⟩, isOpenEmbedding_restrict_proj hs⟩



-- a presheaf is a sheaf iff its prelocal predicate is local ..

variable (F)


variable (X : Type*) [TopologicalSpace X] (p : C(X, B))

def adjunction : {f : C(F.EtaleSpace, X) // p.comp f = proj F} ≃
    {f : (Π U, F.obj U → (sheafOfSections p).1.obj U) //
      ∀ U V (i : U ⟶ V), (sheafOfSections p).1.map i ∘ f U = f V ∘ F.map i} where
  toFun := _
  invFun := _
  left_inv := _
  right_inv := _

-- the opens in the etale space of a local predicate are exactly images of germMap .. no, only if proj is injective on the open

-- many functors!
-- Presheaf B -EtaleSpace→ LocalHomeo/B -sections→ Sheaf B : composition NatIso to sheafification ..
-- Presheaf -sheafification→ Sheaf -forget→ Presheaf .. adjunction such that one composition is iso to identity ..





variable {X : Type*} [TopologicalSpace X] {B : TopCat}

/-- The continuous sections of a (not necessarily continuous) function between two
  topological spaces form a sheaf over the base space. -/
def sheafOfSections (p : X → B) : B.Sheaf (Type _) :=
  B.subsheafToTypes <| (B.continuousLocal X).and <| B.isSection p

/-- The stalks of the sheaf of sections are in bijections with the fibers. -/
def stalkSectionsEquivFiber (p : X → B) (b : B) :
    (sheafOfSections p).presheaf.stalk b ≃ p ⁻¹' {b} where
  toFun := ⟨_, _⟩
  invFun := _
  left_inv := _
  right_inv := _


-- stalks of this sheaf is equiv to fibers of p?
-- should be the case since sheafification preserves stalks

-- Right adjoint is fully faithful iff the counit is an isomorphism  ...
-- "reflection", coreflection -- reflective
-- idempotent adjunction: reflective, coreflective
-- monadic adjunction

-- sections can be considered to be morphisms between certain objects of Top/B .. Yoneda?
-- use open set in B as "test objects"


def EtaleSpaceOver (B : TopCat) : Type _ :=
  ObjectProperty.FullSubcategory fun f : Over B ↦ IsLocalHomeomorph f.hom
