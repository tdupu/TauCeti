/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.StrictHenselization.BaseChange
public import TauCeti.RingTheory.Etale.StandardEtale.Localization

/-!
# Refinement of neighbourhoods over a localization

When `S = M⁻¹R` is a localization and `Ω` is a field over `S`, every pointed étale neighbourhood
of `S` maps into the base change `Neighbourhood.baseChange S (AlgHom.id R Ω)` of a pointed
neighbourhood of `R`
(`Neighbourhood.exists_hom_baseChange_obj`). This is the first half of the finality of
`baseChange S (AlgHom.id R Ω)` proved in `Localization.Final`.

A neighbourhood of `S` is standard étale after inverting an element that is nonzero at the point
(`Neighbourhood.exists_ne_zero_isStandardEtale_away`); a standard étale presentation over `S`
descends to `R` by `StandardEtalePair.exists_map_eq_scaleRoots` and
`StandardEtalePair.exists_lift_comp_eq_of_isUnit`.

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

section Refinement

variable {R S : Type u} {Ω : Type v} [CommRing R] [CommRing S] [Field Ω]
  [Algebra R S] [Algebra R Ω] [Algebra S Ω] [IsScalarTower R S Ω]
  (M : Submonoid R) [IsLocalization M S]

include M in
/-- A pointed neighbourhood of `S = M⁻¹R` maps into the base change of a pointed standard étale
algebra over `R`, compatibly with the points. -/
private theorem exists_lift_comp_eq_point (B : Neighbourhood S Ω) :
    ∃ (U : StandardEtalePair R) (pointU : U.Ring →ₐ[R] Ω)
      (raw : B.obj.left →ₐ[S] S ⊗[R] U.Ring),
      (Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId S Ω) pointU).comp raw = B.point := by
  obtain ⟨f, hf, hfstd⟩ := exists_ne_zero_isStandardEtale_away B
  -- Descend a standard étale presentation of the localization at `f`.
  let L := away B f (isUnit_iff_ne_zero.mpr hf)
  -- The instance transfers along the definitional equality `L.obj.left = Localization.Away f`.
  have : Algebra.IsStandardEtale S L.obj.left := hfstd
  let P : StandardEtalePresentation S L.obj.left :=
    Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some
  have hξ : P.P.HasMap (L.point P.x) := P.hasMap.map L.point
  obtain ⟨b, c, U, G, hU, hG, hg⟩ := StandardEtalePair.exists_map_eq_scaleRoots M P.P
  obtain ⟨pointU, rawP, -, hrawP⟩ :=
    StandardEtalePair.exists_lift_comp_eq_of_isUnit P.P (L.point P.x) hξ (b : R) (c : R) U G
      (IsLocalization.map_units S b) (IsLocalization.map_units S c) hU hG hg
  refine ⟨U, pointU, (rawP.comp P.equivRing.toAlgHom).comp (awayHom B f _).hom.left.hom, ?_⟩
  calc _ = ((Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId S Ω) pointU).comp
            (rawP.comp P.equivRing.toAlgHom)).comp
            (awayHom B f (isUnit_iff_ne_zero.mpr hf)).hom.left.hom :=
        (AlgHom.comp_assoc _ _ _).symm
    _ = L.point.comp (awayHom B f (isUnit_iff_ne_zero.mpr hf)).hom.left.hom := by
      congr 1
      rw [← AlgHom.comp_assoc, hrawP]
      exact P.hom_ext (by simp)
    _ = B.point := point_comp_hom _

end Refinement

section BaseChange

variable {R S : Type u} {Ω : Type v} [CommRing R] [CommRing S] [Field Ω]
  [Algebra R S] [Algebra R Ω] [Algebra S Ω] [IsScalarTower R S Ω]
  (M : Submonoid R) [IsLocalization M S]

include M in
/-- Every pointed neighbourhood of `S = M⁻¹R` maps to the base change of a pointed neighbourhood
of `R`. -/
theorem exists_hom_baseChange_obj (B : Neighbourhood S Ω) :
    ∃ Y : Neighbourhood R Ω, Nonempty (B ⟶ (baseChange S (AlgHom.id R Ω)).obj Y) := by
  obtain ⟨U, pointU, raw, hraw⟩ := exists_lift_comp_eq_point M B
  -- `U.Ring` lives in `Type u`, so lift it to the universe of the neighbourhoods.
  let e : ULift.{v} U.Ring ≃ₐ[R] U.Ring := ULift.algEquiv
  have : Algebra.Etale R (ULift.{v} U.Ring) := Algebra.Etale.of_equiv e.symm
  refine ⟨mk' (ULift.{v} U.Ring) (pointU.comp e.toAlgHom),
    ⟨homMk' ((Algebra.TensorProduct.map (AlgHom.id S S) e.symm.toAlgHom).comp raw) ?_⟩⟩
  have key : (Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId S Ω)
      (pointU.comp e.toAlgHom)).comp (Algebra.TensorProduct.map (AlgHom.id S S) e.symm.toAlgHom) =
      Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId S Ω) pointU := by
    apply Algebra.TensorProduct.ext'
    intro s u
    simp
  rw [point_baseChange_obj, baseChangePoint_def, point_mk']
  -- `AlgHom.id_comp` cannot rewrite here: `pointU.comp e` is typed on `ULift U.Ring`, not on the
  -- carrier `(mk' …).obj.left`; the two forms of the point agree by unfolding `mk'`.
  exact ((AlgHom.comp_assoc _ _ _).symm.trans (congrArg (fun q => q.comp raw) key)).trans hraw

end BaseChange

end TauCeti.StrictHenselization.Neighbourhood
