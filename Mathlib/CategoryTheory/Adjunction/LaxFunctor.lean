/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor

/-!
# Lax endofunctor of Cat induced by a family of adjunctions
-/

universe v u v' u'

namespace CategoryTheory

open Functor

variable {T : Cat.{v, u} → Cat.{v', u'}}
variable {F : ∀ C : Cat, C ⥤ T C} {G : ∀ C, T C ⥤ C}

def OplaxFunctor.ofAdjunction (adj : ∀ C, F C ⊣ G C) : OplaxFunctor Cat Cat where
  obj := T
  map f := G _ ⋙ f ⋙ F _
  map₂ h := (G _).whiskerLeft (whiskerRight h (F _))
  mapId C := (G C).whiskerLeft (leftUnitor _).hom ≫ (adj C).counit
  mapComp f g := whiskerLeft _ (associator ..).hom ≫ (associator ..).inv ≫
    whiskerRight (whiskerLeft _ ((rightUnitor _).inv ≫ whiskerLeft _ (adj _).unit ≫
      (associator ..).inv) ≫ (associator ..).inv) _ ≫ (associator ..).hom
  map₂_id _ := by rw [whiskerRight_id', whiskerLeft_id']
  map₂_comp _ _ := by rw [whiskerRight_comp, whiskerLeft_comp]
  mapComp_naturality_left η g := by
    sorry

  mapComp_naturality_right := _
  map₂_associator := _
  map₂_leftUnitor _ := by
    simp [Bicategory.leftUnitor, Bicategory.whiskerRight]
  map₂_rightUnitor := _

/-   isoWhiskerLeft _ (associator ..) ≪≫ (isoWhiskerRight (associator .. ≪≫ isoWhiskerLeft _
    (associator .. ≪≫ isoWhiskerLeft _ (Equivalence.counitIso ..) ≪≫ rightUnitor ..)) _ ≪≫
    associator ..).symm ≪≫ associator .. (for the equivalence / pseudofunctor version) -/
end CategoryTheory
