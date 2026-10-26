/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.BaseChange
public import TauCeti.RingTheory.StrictHenselization.Filtered
public import TauCeti.RingTheory.StrictHenselization.Localization.Basic
public import TauCeti.RingTheory.TensorProduct.Maps
public import TauCeti.RingTheory.Unramified.Diagonal
public import Mathlib.CategoryTheory.Filtered.Final

/-!
# Finality of pointed étale base change

For a localization `R → S = M⁻¹R` and a field `Ω` over `S`, base change
`Neighbourhood.baseChange S (AlgHom.id R Ω) : Neighbourhood R Ω ⥤ Neighbourhood S Ω` is final.

By `Neighbourhood.exists_hom_baseChange_obj`, every pointed neighbourhood of `S` maps into a base
change. Two parallel maps into a base change are equalized after refining the neighbourhood of
`R`: their difference is a multiple of the image `d` of the unramified diagonal idempotent, hence
killed by `1 - d`; since `d` vanishes at the point, `1 - d` can be inverted after clearing a
denominator from `M`.

## Main results

* `Neighbourhood.exists_hom_isUnit_map_one_sub`: if `d ∈ S ⊗[R] Y` vanishes at the point, then
  `1 - d` becomes a unit after refining `Y`.
* `Neighbourhood.exists_hom_comp_baseChange_map_eq`: parallel maps into a base change are equalized.
* `Neighbourhood.final_baseChange`: base change along a localization is final.

## References

* Stacks Project, Tag 04GW.
* Taylor Dupuy, Thomas Tucker, and Zhuoran Wang, pcfawd-formalization at `9a20b3f`,
  `StrictHenselizationLocalize.lean` and `StrictHenselizationConstruction.lean`.
-/

public section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace TauCeti.StrictHenselization.Neighbourhood

section

variable {R S : Type u} {Ω : Type v} [CommRing R] [CommRing S] [CommRing Ω]
  [Algebra R S] [Algebra R Ω] [Algebra S Ω] [IsScalarTower R S Ω]
  (M : Submonoid R) [IsLocalization M S]

include M in
/-- If `d ∈ S ⊗[R] Y` vanishes at the point of the base change of `Y`, then `1 - d` becomes a
unit after refining `Y` to a neighbourhood `Y'`. -/
theorem exists_hom_isUnit_map_one_sub (Y : Neighbourhood R Ω) (d : S ⊗[R] Y.obj.left)
    (hpoint : baseChangePoint S (AlgHom.id R Ω) Y d = 0) :
    ∃ (Y' : Neighbourhood R Ω) (h : Y ⟶ Y'),
      IsUnit (Algebra.TensorProduct.map (AlgHom.id S S) h.hom.left.hom (1 - d)) := by
  -- Clear the denominator of `1 - d`: `m * (1 - d) = 1 ⊗ y`, and `y` is a unit at the point.
  obtain ⟨⟨y, ⟨m, hm⟩⟩, hy⟩ := IsLocalizedModule.surj M (TensorProduct.mk R S Y.obj.left 1) (1 - d)
  replace hy : algebraMap R (S ⊗[R] Y.obj.left) m * (1 - d) = 1 ⊗ₜ[R] y := by
    simpa [Submonoid.smul_def, Algebra.smul_def] using hy
  have hpointy : Y.point y = algebraMap R Ω m := by
    have h := congrArg (baseChangePoint S (AlgHom.id R Ω) Y) hy
    rw [map_mul, baseChangePoint_algebraMap, map_sub, map_one, hpoint] at h
    simpa using h.symm
  have hyunit : IsUnit (Y.point y) := by
    rw [hpointy]
    rw [IsScalarTower.algebraMap_apply R S Ω]
    exact (IsLocalization.map_units S (⟨m, hm⟩ : M)).map _
  -- Invert `y`; then `m * (1 - d)` and hence `1 - d` becomes a unit.
  obtain ⟨Y', h, hyu⟩ := exists_refinement_isUnit Y y hyunit
  refine ⟨Y', h, ?_⟩
  have hu : IsUnit (Algebra.TensorProduct.map (AlgHom.id S S) h.hom.left.hom
      (algebraMap R (S ⊗[R] Y.obj.left) m * (1 - d))) := by
    rw [hy, Algebra.TensorProduct.map_tmul, map_one]
    exact hyu.map (Algebra.TensorProduct.includeRight : _ →ₐ[R] S ⊗[R] _)
  rw [map_mul] at hu
  exact isUnit_of_mul_isUnit_right hu

include M in
/-- Parallel maps from a pointed neighbourhood of `S` into a base change are equalized by
refining the neighbourhood of `R`. -/
theorem exists_hom_comp_baseChange_map_eq {B : Neighbourhood S Ω} {Y : Neighbourhood R Ω}
    (s t : B ⟶ (baseChange S (AlgHom.id R Ω)).obj Y) :
    ∃ (Y' : Neighbourhood R Ω) (h : Y ⟶ Y'),
      s ≫ (baseChange S (AlgHom.id R Ω)).map h = t ≫ (baseChange S (AlgHom.id R Ω)).map h := by
  let sr : B.obj.left →ₐ[S] S ⊗[R] Y.obj.left := s.hom.left.hom
  let tr : B.obj.left →ₐ[S] S ⊗[R] Y.obj.left := t.hom.left.hom
  obtain ⟨e, he, hker⟩ :=
    TauCeti.Algebra.FormallyUnramified.exists_isIdempotentElem_ker_lmul_eq_span S B.obj.left
  -- The diagonal idempotent `d` vanishes at the point of the base change.
  have hs : (baseChangePoint S (AlgHom.id R Ω) Y).comp sr = B.point := by
    rw [← point_baseChange_obj]
    exact point_comp_hom s
  have ht : (baseChangePoint S (AlgHom.id R Ω) Y).comp tr = B.point := by
    rw [← point_baseChange_obj]
    exact point_comp_hom t
  have hzero : baseChangePoint S (AlgHom.id R Ω) Y (Algebra.TensorProduct.productMap sr tr e) = 0 :=
    Algebra.TensorProduct.map_productMap_eq_zero_of_comp_eq
      (RingHom.mem_ker.mp (hker ▸ Ideal.mem_span_singleton_self e))
      (baseChangePoint S (AlgHom.id R Ω) Y) (hs.trans ht.symm)
  obtain ⟨Y', h, hu⟩ := exists_hom_isUnit_map_one_sub M Y _ hzero
  refine ⟨Y', h, ?_⟩
  apply hom_ext
  simp only [comp_hom_left_hom, baseChange_map_hom_left_hom]
  exact TauCeti.Algebra.FormallyUnramified.comp_eq_comp_of_isUnit_one_sub_productMap
    he hker.le sr tr (Algebra.TensorProduct.map (AlgHom.id S S) h.hom.left.hom) hu

end

section

variable {R S : Type u} {Ω : Type v} [CommRing R] [CommRing S] [Field Ω]
  [Algebra R S] [Algebra R Ω] [Algebra S Ω] [IsScalarTower R S Ω]
  (M : Submonoid R) [IsLocalization M S]

include M in
/-- Base change along a localization is final on pointed neighbourhoods. Stacks, Tag 04GW,
presents the strict henselization as the colimit over pointed étale neighbourhoods; this finality
step is used toward its compatibility with localization. -/
theorem final_baseChange : (baseChange S (AlgHom.id R Ω)).Final := by
  apply Functor.final_of_exists_of_isFiltered
  · exact exists_hom_baseChange_obj M
  · intro B Y s t
    exact exists_hom_comp_baseChange_map_eq M s t

end

end TauCeti.StrictHenselization.Neighbourhood
