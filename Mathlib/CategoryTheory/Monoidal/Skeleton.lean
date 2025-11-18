/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.CategoryTheory.Skeletal

/-!
# The monoid on the skeleton of a monoidal category

The skeleton of a monoidal category is a monoid.

## Main results

* `Skeleton.instMonoid`, for monoidal categories.
* `Skeleton.instCommMonoid`, for braided monoidal categories.

-/


namespace CategoryTheory

open MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- If `C` is monoidal and skeletal, it is a monoid.
See note [reducible non-instances]. -/
abbrev monoidOfSkeletalMonoidal (hC : Skeletal C) : Monoid C where
  mul X Y := X ⊗ Y
  one := 𝟙_ C
  one_mul X := hC ⟨λ_ X⟩
  mul_one X := hC ⟨ρ_ X⟩
  mul_assoc X Y Z := hC ⟨α_ X Y Z⟩

/-- If `C` is braided and skeletal, it is a commutative monoid. -/
def commMonoidOfSkeletalBraided [BraidedCategory C] (hC : Skeletal C) : CommMonoid C :=
  { monoidOfSkeletalMonoidal hC with mul_comm := fun X Y => hC ⟨β_ X Y⟩ }

namespace Skeleton

abbrev tensorObj : Skeleton C → Skeleton C → Skeleton C :=
  Quotient.map₂ (· ⊗ ·) fun _ _ ⟨ea⟩ _ _ ⟨eb⟩ ↦ ⟨ea ⊗ᵢ eb⟩

abbrev tensorObj_eq {X Y : Skeleton C} : tensorObj X Y = toSkeleton (X.out ⊗ Y.out) := by
  obtain ⟨X⟩ := X; obtain ⟨Y⟩ := Y
  let φ := (skeletonEquivalence C).symm.unitIso.app
  exact Quotient.sound ⟨φ X ⊗ᵢ φ Y⟩

/-- The skeleton of a monoidal category has a monoidal structure itself, induced by the equivalence.
-/
noncomputable instance instMonoidalCategory : MonoidalCategory (Skeleton C) :=
  Monoidal.transport (skeletonEquivalence C).symm |>.copyTensorObj _
    tensorObj fun _ _ ↦ eqToIso tensorObj_eq.symm

/--
The skeleton of a monoidal category can be viewed as a monoid, where the multiplication is given by
the tensor product, and satisfies the monoid axioms since it is a skeleton.
-/
noncomputable instance instMonoid : Monoid (Skeleton C) :=
  monoidOfSkeletalMonoidal (skeleton_isSkeleton _).skel

theorem mul_eq (X Y : Skeleton C) : X * Y = toSkeleton (X.out ⊗ Y.out) := tensorObj_eq
theorem one_eq : (1 : Skeleton C) = toSkeleton (𝟙_ C) := rfl

theorem toSkeleton_tensorObj (X Y : C) : toSkeleton (X ⊗ Y) = toSkeleton X * toSkeleton Y := rfl

/-- The skeleton of a braided monoidal category has a braided monoidal structure itself, induced by
the equivalence. -/
noncomputable instance instBraidedCategory [BraidedCategory C] : BraidedCategory (Skeleton C) :=
  BraidedCategory.ofFullyFaithful
    (Monoidal.equivalenceTransported (skeletonEquivalence C).symm).inverse |>.copyTensorObj ..

/--
The skeleton of a braided monoidal category can be viewed as a commutative monoid, where the
multiplication is given by the tensor product, and satisfies the monoid axioms since it is a
skeleton.
-/
noncomputable instance instCommMonoid [BraidedCategory C] : CommMonoid (Skeleton C) :=
  commMonoidOfSkeletalBraided (skeleton_isSkeleton _).skel

end Skeleton

section Monoidal

open Functor

instance : (toSkeletonFunctor C).Monoidal where


instance : (fromSkeleton C).Monoidal where
  ε := (preCounitIso _).inv
  μ X Y := _
  η := (preCounitIso _).hom
  δ X Y := _



variable {D : Type*} [Category D] [MonoidalCategory D] (F : C ⥤ D) (e : C ≌ D)

-- these do not work
noncomputable instance [F.LaxMonoidal] : F.mapSkeleton.LaxMonoidal where
  ε := (toSkeletonFunctor D).map (LaxMonoidal.ε F)
  μ X Y := by
    refine X.hrecOn (fun X ↦ Y.hrecOn ((toSkeletonFunctor D).map <| LaxMonoidal.μ F X ·)
      fun Y Y' ↦ ?_) fun X X' ↦ ?_
    · sorry -- false
    · sorry -- false

noncomputable instance [F.OplaxMonoidal] : F.mapSkeleton.OplaxMonoidal where
  η := (toSkeletonFunctor D).map (OplaxMonoidal.η F)
  δ X Y := by
    refine X.hrecOn (fun X ↦ Y.hrecOn ((toSkeletonFunctor D).map <| OplaxMonoidal.δ F X ·)
      fun Y Y' ⟨e⟩ ↦ ?_) fun X X' ↦ ?_
    · obtain ⟨Y⟩ := Y; rintro ⟨e⟩
      show (toSkeletonFunctor D).map _ ≍ (toSkeletonFunctor D).map _

    sorry

-- TODO: Braided, Symmetric
noncomputable instance [F.Monoidal] : F.mapSkeleton.Monoidal where
  ε_η := ((toSkeletonFunctor D).map_comp ..).symm.trans <| by simp; rfl
  η_ε := ((toSkeletonFunctor D).map_comp ..).symm.trans <| by simp; rfl
  μ_δ := by rintro ⟨⟩ ⟨⟩; exact ((toSkeletonFunctor D).map_comp ..).symm.trans <| by simp; rfl
  δ_μ := by rintro ⟨⟩ ⟨⟩; exact ((toSkeletonFunctor D).map_comp ..).symm.trans <| by simp; rfl

/-- A monoidal functor between skeletal monoidal categories induces a monoid homomorphism. -/
def Skeletal.monoidHom [F.Monoidal] (hC : Skeletal C) (hD : Skeletal D) :
    let _ := monoidOfSkeletalMonoidal hC
    let _ := monoidOfSkeletalMonoidal hD
    C →* D :=
  let _ := monoidOfSkeletalMonoidal hC
  let _ := monoidOfSkeletalMonoidal hD
  { toFun := F.obj
    map_one' := hD ⟨(Monoidal.εIso F).symm⟩
    map_mul' X Y := hD ⟨(Monoidal.μIso F X Y).symm⟩ }

/-- A monoidal functor between monoidal categories induces a monoid homomorphism between
the skeleta. -/
noncomputable def Skeleton.monoidHom [F.Monoidal] : Skeleton C →* Skeleton D :=
  (skeleton_skeletal C).monoidHom F.mapSkeleton (skeleton_skeletal D)

/-- A monoidal equivalence between skeletal monoidal categories induces a monoid isomorphism. -/
def Skeletal.mulEquiv [e.functor.Monoidal] (hC : Skeletal C) (hD : Skeletal D) :
    let _ := monoidOfSkeletalMonoidal hC
    let _ := monoidOfSkeletalMonoidal hD
    C ≃* D :=
  let _ := monoidOfSkeletalMonoidal hC
  let _ := monoidOfSkeletalMonoidal hD
  { toFun := e.functor.obj
    invFun := e.inverse.obj
    left_inv X := hC ⟨(e.unitIso.app X).symm⟩
    right_inv X := hD ⟨e.counitIso.app X⟩
    map_mul' X Y := hD ⟨(Monoidal.μIso e.functor X Y).symm⟩ }

/-- A monoidal equivalence between monoidal categories induces a monoid isomorphism between
the skeleta. -/
noncomputable def Skeleton.mulEquiv [e.functor.Monoidal] : Skeleton C ≃* Skeleton D :=
  (skeleton_skeletal C).mulEquiv e.mapSkeleton (skeleton_skeletal D)

end Monoidal

end CategoryTheory
