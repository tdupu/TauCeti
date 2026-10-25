/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Localization.Integral
public import TauCeti.RingTheory.Polynomial.ScaleRoots

/-!
# Standard étale pairs over a localization

Let `S = M⁻¹R` be a localization. A standard étale pair `P` over `S` is descended to `R` by
clearing denominators and scaling its roots by a denominator `b ∈ M`: the resulting pair `U` over
`R` has `U.f` mapping to `P.f.scaleRoots b`, and `U.g = U.f' * G` with `G` mapping to a multiple
of `P.g.scaleRoots b`.

## Main results

* `StandardEtalePair.exists_map_eq_scaleRoots`: the descent to `R`.
* `StandardEtalePair.hasMap_algebraMap_mul_of_hasMap` and
  `StandardEtalePair.hasMap_of_hasMap_algebraMap_mul`: a point of `P` at `x` gives a point of the
  descended pair at `b * x` when `b` and `c` are units, and conversely when `b` is a unit.
* `StandardEtalePair.exists_lift_comp_eq_of_isUnit`: a point `ξ` of `P` in an `S`-algebra
  `Ω` factors through `S ⊗[R] U.Ring` for a descended pair `U` over `R`, with the point `b * ξ`
  of `U`.

## References

* Stacks Project, Tag 04GW: the strict henselization is the colimit of pointed étale
  neighbourhoods; this file is the generic descent step for comparing such colimits along a
  localization.
* Taylor Dupuy, Thomas Tucker, and Zhuoran Wang, pcfawd-formalization at `9a20b3f`
  (Apache 2.0), `StrictHenselizationLocalize.lean`: the descent of a standard étale presentation
  along a localization by clearing denominators and scaling roots.
-/

public section

open Polynomial
open scoped TensorProduct

namespace StandardEtalePair

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (M : Submonoid R) [IsLocalization M S]

/-- Clearing denominators: for a standard étale pair `P` over `S = M⁻¹R`, there are `b, c ∈ M`, a
standard étale pair `U` over `R` and a polynomial `G` over `R` such that `U.f` maps to
`P.f.scaleRoots b`, `G` maps to `c • P.g.scaleRoots b`, and `U.g = U.f' * G`. -/
theorem exists_map_eq_scaleRoots (P : StandardEtalePair S) :
    ∃ (b c : M) (U : StandardEtalePair R) (G : R[X]),
      U.f.map (algebraMap R S) = P.f.scaleRoots (algebraMap R S b) ∧
      G.map (algebraMap R S) =
        (c : R) • P.g.scaleRoots (algebraMap R S b) ∧
      U.g = derivative U.f * G := by
  -- Scale the roots of `f` by a common denominator, so that it lifts to a monic polynomial.
  let b : M := IsLocalization.commonDenom M P.f.support P.f.coeff
  have hlift := IsLocalization.scaleRoots_commonDenom_mem_lifts M P.f
    (by rw [P.monic_f.leadingCoeff]; exact ⟨1, map_one _⟩)
  obtain ⟨F, hFmap, -, hFmonic⟩ :=
    lifts_and_natDegree_eq_and_monic hlift
      ((monic_scaleRoots_iff _).mpr P.monic_f)
  -- Clear the denominators of the scaled `g`.
  let G := IsLocalization.integerNormalization M
    (P.g.scaleRoots (algebraMap R S b))
  obtain ⟨c, hcM, hGmap⟩ :=
    IsLocalization.integerNormalization_spec M
      (P.g.scaleRoots (algebraMap R S b))
  let U : StandardEtalePair R :=
    ⟨F, hFmonic, derivative F * G, G, 0, 1, by ring⟩
  exact ⟨b, ⟨c, hcM⟩, U, G, hFmap, hGmap, rfl⟩

end

section

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]

/-- A point `x` of `P` gives a point `b * x` of the descended pair `U`, when `b` and `c` are
units in `A`. -/
theorem hasMap_algebraMap_mul_of_hasMap
    (P : StandardEtalePair S) (U : StandardEtalePair R) (G : R[X])
    (b c : R) (x : A)
    (hf : U.f.map (algebraMap R S) = P.f.scaleRoots (algebraMap R S b))
    (hg : U.g = U.f.derivative * G)
    (hG : G.map (algebraMap R S) =
      c • P.g.scaleRoots (algebraMap R S b))
    (hb : IsUnit (algebraMap R A b)) (hc : IsUnit (algebraMap R A c))
    (hx : P.HasMap x) : U.HasMap (algebraMap R A b * x) := by
  constructor
  · rw [← aeval_map_algebraMap S, hf, scaleRoots_aeval_algebraMap_mul, hx.1, mul_zero]
  · have hbS : IsUnit (algebraMap S A (algebraMap R S b)) := by
      rw [← IsScalarTower.algebraMap_apply R S A b]
      exact hb
    have hderiv : IsUnit (aeval (algebraMap R A b * x) U.f.derivative) := by
      rw [← aeval_map_algebraMap S, ← derivative_map, hf,
        IsScalarTower.algebraMap_apply R S A b]
      exact isUnit_aeval_derivative_scaleRoots P.f (algebraMap R S b) x hbS
        hx.isUnit_derivative_f
    have hGunit : IsUnit (aeval (algebraMap R A b * x) G) := by
      rw [aeval_eq_of_map_eq_smul_scaleRoots P.g G b c x hG]
      exact hc.mul ((hb.pow _).mul hx.2)
    rw [hg, map_mul]
    exact hderiv.mul hGunit

/-- Conversely, a point `b * x` of the descended pair `U` gives a point `x` of `P`, when `b` is a
unit in `A`. -/
theorem hasMap_of_hasMap_algebraMap_mul
    (P : StandardEtalePair S) (U : StandardEtalePair R) (G : R[X])
    (b c : R) (x : A)
    (hf : U.f.map (algebraMap R S) = P.f.scaleRoots (algebraMap R S b))
    (hg : U.g = U.f.derivative * G)
    (hG : G.map (algebraMap R S) =
      c • P.g.scaleRoots (algebraMap R S b))
    (hb : IsUnit (algebraMap R A b))
    (hU : U.HasMap (algebraMap R A b * x)) : P.HasMap x := by
  constructor
  · have hroot : aeval (algebraMap R A b * x) (P.f.scaleRoots (algebraMap R S b)) = 0 := by
      rw [← hf, aeval_map_algebraMap S]
      exact hU.1
    rw [scaleRoots_aeval_algebraMap_mul] at hroot
    exact (hb.pow _).mul_right_eq_zero.mp hroot
  · have hGunit : IsUnit (aeval (algebraMap R A b * x) G) := by
      have hunit := hU.2
      rw [hg, map_mul] at hunit
      exact isUnit_of_mul_isUnit_right hunit
    rw [aeval_eq_of_map_eq_smul_scaleRoots P.g G b c x hG] at hGunit
    exact isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right hGunit)

end

section

variable {R S Ω : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing Ω] [Algebra R Ω]
  [Algebra S Ω] [IsScalarTower R S Ω]

/-- A point `ξ` of a standard étale pair `P` over `S` in an `S`-algebra `Ω` factors through the
base change `S ⊗[R] U.Ring`, where `U` is a pair over `R` descending `P` as in
`exists_map_eq_scaleRoots` (with denominators `b`, `c`, units in `S`, and cleared polynomial `G`).
The point `pointU` of `U` in `Ω` is `b * ξ`. -/
theorem exists_lift_comp_eq_of_isUnit
    (P : StandardEtalePair S) (ξ : Ω) (hξ : P.HasMap ξ) (b c : R) (U : StandardEtalePair R)
    (G : R[X]) (hbS : IsUnit (algebraMap R S b)) (hcS : IsUnit (algebraMap R S c))
    (hf : U.f.map (algebraMap R S) = P.f.scaleRoots (algebraMap R S b))
    (hG : G.map (algebraMap R S) = c • P.g.scaleRoots (algebraMap R S b))
    (hg : U.g = derivative U.f * G) :
    ∃ (pointU : U.Ring →ₐ[R] Ω) (raw : P.Ring →ₐ[S] S ⊗[R] U.Ring),
      pointU U.X = algebraMap R Ω b * ξ ∧
      (Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId S Ω) pointU).comp raw =
        P.lift ξ hξ := by
  -- Outline: take the point of `U` at `b ξ`, and unscale `1 ⊗ X`.
  let T := S ⊗[R] U.Ring
  have hbΩ : IsUnit (algebraMap R Ω b) :=
    by rw [IsScalarTower.algebraMap_apply R S Ω]; exact hbS.map _
  have hcΩ : IsUnit (algebraMap R Ω c) :=
    by rw [IsScalarTower.algebraMap_apply R S Ω]; exact hcS.map _
  have hUξ : U.HasMap (algebraMap R Ω b * ξ) :=
    hasMap_algebraMap_mul_of_hasMap P U G b c ξ hf hg hG hbΩ hcΩ hξ
  let pointU : U.Ring →ₐ[R] Ω := U.lift _ hUξ
  have hbT : IsUnit (algebraMap R T b) :=
    by rw [IsScalarTower.algebraMap_apply R S T]; exact hbS.map _
  let w : T := (Algebra.TensorProduct.includeRight : U.Ring →ₐ[R] T) U.X
  have hw : U.HasMap w :=
    U.hasMap_X.map (Algebra.TensorProduct.includeRight : U.Ring →ₐ[R] T)
  let z : T := ↑(hbT.unit⁻¹) * w
  have hscale : algebraMap R T b * z = w := by
    rw [← mul_assoc, IsUnit.mul_val_inv, one_mul]
  have hz : P.HasMap z := by
    apply hasMap_of_hasMap_algebraMap_mul P U G b c z hf hg hG hbT
    rw [hscale]
    exact hw
  let raw : P.Ring →ₐ[S] T := P.lift z hz
  let pointT : T →ₐ[S] Ω :=
    Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId S Ω) pointU
  have hwpoint : pointT w = algebraMap R Ω b * ξ := by
    simp only [pointT, w, Algebra.TensorProduct.includeRight_apply]
    rw [Algebra.TensorProduct.lift_tmul]
    simp [pointU]
  have hzpoint : pointT z = ξ := by
    have h := congrArg pointT hscale
    rw [map_mul, hwpoint] at h
    have hmap : pointT (algebraMap R T b) = algebraMap R Ω b :=
      (pointT.restrictScalars R).commutes b
    rw [hmap] at h
    exact hbΩ.mul_left_cancel h
  refine ⟨pointU, raw, by simp [pointU], ?_⟩
  apply P.hom_ext
  simp [pointT, raw, hzpoint]

end

end StandardEtalePair
