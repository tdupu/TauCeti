/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.ScaleRoots
public import Mathlib.RingTheory.Polynomial.Tower

/-!
# Root scaling: finite products, composition and derivatives

Scaling roots commutes with finite products over a commutative semiring without zero
divisors, and with finite products of monic polynomials over any commutative semiring.
This transports factorizations into linear factors through integral normalization.
Scaling the roots by `s` also multiplies the subleading coefficient by `s`, so it preserves
the vanishing of that coefficient.

Substituting `b * X` into `p.scaleRoots b` undoes the root scaling, up to the factor
`b ^ natDegree`. Differentiating this shows that the derivative of `p.scaleRoots b` at `b * x` is
a unit as soon as `b` and `p'(x)` are units. Over a scalar tower `R → S → A`, evaluating the
scaled polynomial at `algebraMap R A b * x` multiplies the value of `p` at `x` by a power of
`algebraMap R A b` (`scaleRoots_aeval_algebraMap_mul`, `aeval_eq_of_map_eq_smul_scaleRoots`).
-/

public section

namespace Polynomial

section Products

variable {R ι : Type*} [CommSemiring R]

/-- Scaling the roots by `s` multiplies the subleading coefficient by `s`. -/
@[simp]
theorem nextCoeff_scaleRoots (p : R[X]) (s : R) :
    (p.scaleRoots s).nextCoeff = p.nextCoeff * s := by
  rcases Nat.eq_zero_or_pos p.natDegree with h | h
  · simp [nextCoeff, natDegree_scaleRoots, h]
  rw [nextCoeff_of_natDegree_pos (by rwa [natDegree_scaleRoots]), nextCoeff_of_natDegree_pos h,
    natDegree_scaleRoots, coeff_scaleRoots, Nat.sub_sub_self (by omega), pow_one]

/-- Scaling roots commutes with a finite product of monic polynomials, even when the
coefficient semiring has zero divisors. -/
theorem prod_scaleRoots_of_monic (s : Finset ι) (f : ι → R[X]) (a : R)
    (hf : ∀ i ∈ s, (f i).Monic) :
    (∏ i ∈ s, f i).scaleRoots a = ∏ i ∈ s, (f i).scaleRoots a := by
  classical
  nontriviality R
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hfi := hf i (Finset.mem_insert_self i s)
    have hfs : ∀ j ∈ s, (f j).Monic := fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, mul_scaleRoots', ih hfs, Finset.prod_insert hi]
    simp [hfi.leadingCoeff, (monic_prod_of_monic s f hfs).leadingCoeff]

/-- Scaling all roots of a finite product scales the roots of every factor. -/
@[simp]
theorem prod_scaleRoots [NoZeroDivisors R] (s : Finset ι) (f : ι → R[X]) (a : R) :
    (∏ i ∈ s, f i).scaleRoots a = ∏ i ∈ s, (f i).scaleRoots a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi, mul_scaleRoots_of_noZeroDivisors, ih]

end Products

section

variable {R : Type*} [CommSemiring R]

/-- Composing `p.scaleRoots b` with `C b * X` gives `C (b ^ natDegree) * p`: substituting
`b * X` undoes the root scaling. -/
theorem scaleRoots_comp_C_mul_X (p : R[X]) (b : R) :
    (p.scaleRoots b).comp (C b * X) = C (b ^ p.natDegree) * p := by
  have h := scaleRoots_eval₂_mul (p := p) (f := C) (r := X) (s := b)
  simpa only [comp, eval₂_C, eval₂_X, eval₂_mul, eval₂_C_X, map_pow] using h

/-- The derivative version of `Polynomial.scaleRoots_comp_C_mul_X`. -/
theorem C_mul_derivative_scaleRoots_comp_C_mul_X (p : R[X]) (b : R) :
    C b * (p.scaleRoots b).derivative.comp (C b * X) =
      C (b ^ p.natDegree) * p.derivative := by
  have h := congrArg derivative (scaleRoots_comp_C_mul_X p b)
  simpa only [derivative_comp, derivative_C_mul_X, derivative_C_mul, derivative_X,
    mul_one] using h

/-- If `b` and `p'(x)` are units, then the derivative of `p.scaleRoots b` at `b * x` is a unit. -/
theorem isUnit_aeval_derivative_scaleRoots {A : Type*} [CommSemiring A] [Algebra R A]
    (p : R[X]) (b : R) (x : A)
    (hb : IsUnit (algebraMap R A b)) (hp : IsUnit (aeval x p.derivative)) :
    IsUnit (aeval (algebraMap R A b * x) (p.scaleRoots b).derivative) := by
  have h := congrArg (aeval x) (C_mul_derivative_scaleRoots_comp_C_mul_X p b)
  simp only [map_mul, aeval_C, aeval_comp, aeval_X] at h
  have hunit : IsUnit (algebraMap R A b *
      aeval (algebraMap R A b * x) (p.scaleRoots b).derivative) := by
    rw [h, map_pow]
    exact (hb.pow _).mul hp
  exact isUnit_of_dvd_unit ⟨algebraMap R A b, by ring⟩ hunit

end

section

variable {R S A : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring A] [Algebra R S]
  [Algebra S A] [Algebra R A] [IsScalarTower R S A]

/-- Evaluating `p.scaleRoots (algebraMap R S b)` at `algebraMap R A b * x` multiplies the value
of `p` at `x` by `algebraMap R A b ^ natDegree`. -/
theorem scaleRoots_aeval_algebraMap_mul (p : S[X]) (b : R) (x : A) :
    aeval (algebraMap R A b * x) (p.scaleRoots (algebraMap R S b)) =
      algebraMap R A b ^ p.natDegree * aeval x p := by
  simpa [Algebra.smul_def, ← IsScalarTower.algebraMap_apply R S A] using
    scaleRoots_aeval_smul (p := p) x (algebraMap R S b)

/-- If `G` over `R` maps to `c • p.scaleRoots (algebraMap R S b)` over `S`, then `G` at
`algebraMap R A b * x` is `algebraMap R A c * algebraMap R A b ^ natDegree * p x`. -/
theorem aeval_eq_of_map_eq_smul_scaleRoots (p : S[X]) (G : R[X]) (b c : R) (x : A)
    (hG : G.map (algebraMap R S) = c • p.scaleRoots (algebraMap R S b)) :
    aeval (algebraMap R A b * x) G =
      algebraMap R A c * (algebraMap R A b ^ p.natDegree * aeval x p) := by
  rw [← aeval_map_algebraMap S, hG, Algebra.smul_def, map_mul, Polynomial.algebraMap_apply,
    aeval_C, ← IsScalarTower.algebraMap_apply R S A c, scaleRoots_aeval_algebraMap_mul]

end

end Polynomial
