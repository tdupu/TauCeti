/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.RingTheory.Etale.AdjoinRoot

/-!
# Standard tamely ramified covers

For a commutative ring `A`, an element `f` and an exponent `e`, the *standard tamely ramified
cover* of `Spec A` along `f` is `Spec A[x]/(x^e − f)` (Stacks, Example 58.31.4 (0EYF)). Stacks
assumes `A` Noetherian, `f` a nonzerodivisor with `A/fA` reduced and `e ≥ 1` invertible in `A`;
the algebra itself is defined without these hypotheses, and each statement carries the ones it
uses. This file proves that the cover is free of rank `e`, and that when `e` is nonzero and
invertible the cover `A_f[x]/(x^e − f)` of `Spec A_f` is étale; the comparison with the
localization at `f` of the cover over `A` is not proved here.

## Main definitions

* `TauCeti.standardTameCover A f e`: the algebra `A[x]/(x^e − f)`, as `AdjoinRoot (X ^ e - C f)`.
* `TauCeti.IsFiniteProductOfStandardTameCovers A C f`: `C` is `A`-isomorphic to a finite product
  of standard tamely ramified covers along `f` with exponents invertible in `A`, the shape of the
  conclusions of Stacks, Lemmas 58.31.5 (0EYG) and 58.31.6 (0EYH).

## Main results

* `TauCeti.standardTameCover_free`: the cover is free of rank `e`.
* `TauCeti.standardTameCover_etale_of_isUnit`: if `e ≠ 0` and `f` and `e` are units, the cover is
  étale.
* `TauCeti.standardTameCover_etale_away`: if `e ≠ 0` and `e` is a unit, `B[x]/(x^e − f)` is
  étale over any localization `B` of `A` away from `f`.
* `TauCeti.isFiniteProductOfStandardTameCovers_standardTameCover`: a single standard cover is a
  finite product of standard covers.
* `TauCeti.IsFiniteProductOfStandardTameCovers.of_algEquiv`: transport along `A`-algebra
  isomorphisms.

## References

* [Stacks Project, Example 58.31.4](https://stacks.math.columbia.edu/tag/0EYF).
* Ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0): `standardTameCover_free` is
  `Pcf.Kummer.finrank_adjoinRoot_kummerPoly` (`lean/Pcf/Kummer.lean`), there for a unit constant
  term; `standardTameCover_etale_of_isUnit` is `Pcf.Kummer.etale_adjoinRoot_kummerPoly` (same
  file); `standardTameCover_etale_away` is `Pcf.Stacks.localizedStandardCover_etale`
  (`lean/Pcf/Stacks/Abhyankar/StandardCover.lean`); and
  `isFiniteProductOfStandardTameCovers_standardTameCover` is
  `Pcf.Stacks.standardCover_isFiniteDisjointUnionOfStandardTameCovers`
  (`lean/Pcf/Stacks/Abhyankar/StandardCoverBaseCase.lean`).
-/

public section

universe u

open Polynomial

namespace TauCeti

variable (A : Type u) [CommRing A]

/-- The standard tamely ramified cover `A[x]/(x^e − f)`. Stacks, Example 58.31.4 (0EYF). The
algebra is defined without the example's hypotheses; statements carry the ones they use. -/
@[stacks 0EYF "the algebra A[x]/(x^e − f)"]
abbrev standardTameCover (f : A) (e : ℕ) : Type u :=
  AdjoinRoot (X ^ e - C f)

/-- The standard cover is free of rank `e`: the "finite locally free" assertion of Stacks,
Example 58.31.4 (0EYF). -/
@[stacks 0EYF "finite locally free"]
theorem standardTameCover_free [Nontrivial A] (f : A) (e : ℕ) (he : 1 ≤ e) :
    Module.Free A (standardTameCover A f e) ∧ Module.finrank A (standardTameCover A f e) = e := by
  have hmonic : (X ^ e - C f).Monic := monic_X_pow_sub_C f (Nat.one_le_iff_ne_zero.mp he)
  refine ⟨hmonic.free_adjoinRoot, ?_⟩
  rw [(AdjoinRoot.powerBasis' hmonic).finrank, AdjoinRoot.powerBasis'_dim, natDegree_X_pow_sub_C]

variable {A}

/-- If `e ≠ 0` and `f` and `e` are units of `A`, the standard cover `A[x]/(x^e − f)` is
étale over `A`. -/
theorem standardTameCover_etale_of_isUnit {f : A} {e : ℕ} (he : e ≠ 0) (hf : IsUnit f)
    (heu : IsUnit (e : A)) : Algebra.Etale A (standardTameCover A f e) := by
  -- `x^e − u` is monic and separable for units `u` and `e`, so the cover is standard étale.
  obtain ⟨u, rfl⟩ := hf
  have := (monic_X_pow_sub_C (u : A) he).isStandardEtale_adjoinRoot
    (separable_X_pow_sub_C_unit u heu)
  infer_instance

/-- If `e ≠ 0`, `e` is invertible in `A`, and `B` is a localization of `A` away from `f`, then
`B[x]/(x^e − f)` is étale over `B`. This is the "étale over `D(f)`" assertion of Stacks, Example
58.31.4 (0EYF), for the cover built over `A_f`; its comparison with the localization at `f` of the
cover over `A` is not proved here. -/
@[stacks 0EYF "étale over D(f), for the cover built over A_f"]
theorem standardTameCover_etale_away (f : A) {B : Type*} [CommRing B] [Algebra A B]
    [IsLocalization.Away f B] {e : ℕ} (he : e ≠ 0) (heu : IsUnit (e : A)) :
    Algebra.Etale B (standardTameCover B (algebraMap A B f) e) := by
  have heu' : IsUnit (e : B) := by
    simpa only [map_natCast] using heu.map (algebraMap A B)
  exact standardTameCover_etale_of_isUnit he (IsLocalization.Away.algebraMap_isUnit f) heu'

variable (A) in
/-- `C` is `A`-isomorphic to a finite product of standard tamely ramified covers along `f` with
exponents invertible in `A`. No tag: it is the shape of the conclusions of Stacks, Lemmas 58.31.5
(0EYG) and 58.31.6 (0EYH). -/
def IsFiniteProductOfStandardTameCovers (C : Type u) [CommRing C] [Algebra A C] (f : A) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (e : ι → ℕ), (∀ i, 1 ≤ e i) ∧ (∀ i, IsUnit (e i : A)) ∧
    Nonempty (C ≃ₐ[A] ∀ i, standardTameCover A f (e i))

/-- Characterization of finite products of standard tame covers by their indexed family. -/
theorem isFiniteProductOfStandardTameCovers_iff {C : Type u} [CommRing C] [Algebra A C] (f : A) :
    IsFiniteProductOfStandardTameCovers A C f ↔
      ∃ (ι : Type) (_ : Fintype ι) (e : ι → ℕ), (∀ i, 1 ≤ e i) ∧
        (∀ i, IsUnit (e i : A)) ∧ Nonempty (C ≃ₐ[A] ∀ i, standardTameCover A f (e i)) :=
  Iff.rfl

/-- Being a finite product of standard covers is invariant under `A`-algebra isomorphisms. -/
theorem IsFiniteProductOfStandardTameCovers.of_algEquiv {C C' : Type u} [CommRing C]
    [Algebra A C] [CommRing C'] [Algebra A C'] {f : A}
    (h : IsFiniteProductOfStandardTameCovers A C f) (φ : C ≃ₐ[A] C') :
    IsFiniteProductOfStandardTameCovers A C' f := by
  obtain ⟨ι, _, e, he, heu, ⟨ψ⟩⟩ := (isFiniteProductOfStandardTameCovers_iff f).mp h
  exact (isFiniteProductOfStandardTameCovers_iff f).mpr
    ⟨ι, inferInstance, e, he, heu, ⟨φ.symm.trans ψ⟩⟩

/-- A single standard cover is a finite product of standard covers, indexed by a point. -/
theorem isFiniteProductOfStandardTameCovers_standardTameCover (f : A) {e : ℕ} (he : 1 ≤ e)
    (heu : IsUnit (e : A)) :
    IsFiniteProductOfStandardTameCovers A (standardTameCover A f e) f :=
  (isFiniteProductOfStandardTameCovers_iff f).mpr
    ⟨Unit, inferInstance, fun _ ↦ e, fun _ ↦ he, fun _ ↦ heu,
      ⟨(AlgEquiv.funUnique A Unit (standardTameCover A f e)).symm⟩⟩

end TauCeti
