/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Sheaves.LocalPredicate

/-!
# Étale spaces of local predicates and presheaves

The traditional approach to étale spaces startsfrom a (pre)sheaf on a base space and
directly constructs the associated étale space with a local homeomorphism to the base space.
We instead construct a local homeomorphism from an arbitrary type family (over the base space)
with a predicate on sections (over open sets of the base space) specifying the "admissible"
sections, provided that the type family behaves like the family of stalks of the presheaf
of admissible sections (i.e., satisfies the conditions `IsStalkInj` and `IsStalkSurj`).

The passage between (pre)sheaves and (pre)local predicates was already established during
the development of sheafification (see `TopCat.LocalPredicate` and the file
``Mathlib.Topology.Sheaves.Sheafify`), and we obtain the étale space of a (pre)sheaf by
combining both steps. But our theory can also be applied to situations where the type family
is not (definitionally) the stalks of a presheaf: for example it can be a family of Hom types
in the fundamental groupoid when constructing the universal cover, or a constant family
when constructing the primitive of a holomorphic function and integrating it along a path.

In this file we will adopt the sheaf-theoretic terminology and refer to the types in the type
family as "stalks" and their elements as "germs".

## Main definitions

* `EtaleSpace`: The étale space associated to a set of admissible sections given in the form of
  a predicate. It is endowed with the strongest topology making every admissible section continuous.
  `EtaleSpace.mk` is its constructor and `EtaleSpace.proj` is the continuous projection to the
  base space.

## Main results

Some results below requires the type family satisfies the injectivity and/or surjectivity criteria
to behave like the family of stalks of the admissible sections.

* `EtaleSpace.isOpenEmbedding_restrict_proj`: the projection from the étale space
  to the base space is an open embedding on the range of every admissible section.

* `EtaleSpace.isOpenEmbedding_section`: every admissible section is an open embedding
  (requires injectivity criterion).

* `EtaleSpace.isLocalHomeomorph_proj`: the projection from the étale space to the base space
  is a local homeomorphism (requires both criteria).

* `EtaleSpace.isOpen_range_section_iff_of_isOpen`: the range of a section is open if and only if
  it is the range of a continuous section over an open set (requires both criteria).

* `EtaleSpace.continuous_cod_iff`: a function to the étale space is continuous if and only if
  it agrees with an admissible section around each point (requires both criteria).

* `EtaleSpace.continuous_section_iff`: a section is continuous if and only if
  it is admissible according to the sheafified predicate
  (requires both criteria and that the predicate is pre-local).

* `EtaleSpace.isTopologicalBasis`: the étale space has a basis consisting of
  the ranges of admissible sections (with the same requirements as the above).
-/

open CategoryTheory Topology TopologicalSpace Opposite Set

universe u v

namespace TopCat

variable {B : TopCat.{u}} {F : B → Type v}

set_option linter.unusedVariables false in
/-- The underlying type of the étale space associated to a predicate on sections of a type family
is simply the sigma type. -/
@[nolint unusedArguments]
def EtaleSpace (pred : Π ⦃U : Opens B⦄, (Π b : U, F b) → Prop) : Type _ := Σ b, F b

namespace EtaleSpace

variable {pred : Π ⦃U : Opens B⦄, (Π b : U, F b) → Prop}

/-- Constructor for points in the étale space. -/
@[simps] def mk {b : B} (x : F b) : EtaleSpace pred := ⟨b, x⟩

/-- The étale space is endowed with the strongest topology
making every admissible section continuous. -/
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
  continuous_invFun := ((proj _).continuous.comp continuous_subtype_val).subtype_mk <| by
    rintro ⟨_, b, rfl⟩; exact b.2

theorem isOpenEmbedding_restrict_proj :
    IsOpenEmbedding ((range (mk <| s ·)).restrict (proj pred)) :=
  U.2.isOpenEmbedding_subtypeVal.comp (homeomorphRangeSection hs).symm.isOpenEmbedding

theorem isOpen_range_section (inj : ∀ b, IsStalkInj pred b) :
    IsOpen (range fun b ↦ (mk (s b) : EtaleSpace pred)) :=
  isOpen_iff.mpr fun V t ht ↦ isOpen_iff_mem_nhds.mpr fun ⟨v, hv⟩ ⟨⟨u, hu⟩, he⟩ ↦ by
    cases congr($he.1)
    have ⟨W, iU, iV, eq⟩ := inj v ⟨U, hu⟩ ⟨V, hv⟩ _ _ hs ht congr($he.2)
    exact Filter.mem_of_superset ((W.1.2.preimage continuous_subtype_val).mem_nhds W.2)
      fun v hv ↦ ⟨⟨v, iU.le hv⟩, congr(mk $(eq ⟨v, hv⟩))⟩

theorem isOpenEmbedding_section (inj : ∀ b, IsStalkInj pred b) :
    IsOpenEmbedding fun b ↦ (mk (s b) : EtaleSpace pred) := by
  rw [isOpenEmbedding_iff, isEmbedding_iff, and_assoc]
  exact ⟨.of_comp (continuous_section hs) (proj _).continuous .subtypeVal,
    fun _ _ eq ↦ Subtype.ext congr(proj _ $eq), isOpen_range_section hs inj⟩

omit hs

section InjSurj

variable (inj : ∀ b, IsStalkInj pred b) (surj : ∀ b, IsStalkSurj pred b)
include inj surj

theorem isLocalHomeomorph_proj : IsLocalHomeomorph (proj pred) :=
  isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr fun x ↦
    have ⟨_U, _s, hs, eq⟩ := surj _ x.2
    ⟨_, (isOpen_range_section hs inj).mem_nhds ⟨_, congr(mk $eq)⟩, isOpenEmbedding_restrict_proj hs⟩

theorem continuous_cod_iff {X} [TopologicalSpace X] {f : X → EtaleSpace pred} :
    Continuous f ↔ Continuous (proj _ ∘ f) ∧ ∀ x, ∃ (U : OpenNhds (f x).1) (s : Π b : U.1, F b),
      pred s ∧ ∃ V ∈ 𝓝 x, ∀ x' (h' : (f x').1 ∈ U.1), x' ∈ V → s ⟨_, h'⟩ = (f x').2 := by
  refine ⟨fun h ↦ ⟨(proj _).continuous.comp h, fun x ↦ ?_⟩,
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

theorem isOpen_injOn_iff_exists_continuous_section {V : Set (EtaleSpace pred)} :
    IsOpen V ∧ V.InjOn (proj _) ↔ letI U := proj _ '' V
    IsOpen U ∧ ∃ s : Π b : U, F b, letI sec b : EtaleSpace pred := mk (s b)
      Continuous sec ∧ range sec = V := by
  rw [((isLocalHomeomorph_proj inj surj).isOpen_injOn_tfae V).out 0 3 rfl]
  refine and_congr .rfl (.trans ?_ Sigma.piSubtypeEquivSubtypeSigma.exists_congr_left.symm)
  simp_rw [show mk = Sigma.mk _ from rfl, Sigma.mk_mk_piSubtypeEquivSubtypeSigma]
  exact ⟨fun ⟨s, hs, hsV⟩ ↦ ⟨⟨s, hs⟩, s.continuous, hsV⟩, fun ⟨s, hs, hsV⟩ ↦ ⟨⟨s.1, hs⟩, s.2, hsV⟩⟩

theorem isOpen_range_section_iff_of_isOpen {U : Set B} {s : Π b : U, F b} :
    letI sec b : EtaleSpace pred := mk (s b)
    IsOpen (range sec) ↔ IsOpen U ∧ Continuous sec :=
  (isLocalHomeomorph_proj inj surj).isOpen_range_section_iff U rfl

theorem isOpen_range_section_iff :
    letI sec b : EtaleSpace pred := mk (s b)
    IsOpen (range sec) ↔ Continuous sec :=
  (isOpen_range_section_iff_of_isOpen inj surj).trans <| and_iff_right U.2

end InjSurj

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

end Section

end EtaleSpace

end TopCat
