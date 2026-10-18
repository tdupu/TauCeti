/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# Unramified, tamely and totally ramified extensions of a discrete valuation ring

Let `A` be a discrete valuation ring and `L` a field containing `A`, and let `B` be the integral
closure of `A` in `L`. The extension is measured at the maximal ideals `P` of `B` lying over the
maximal ideal of `A`, through the ramification index `e(P)` (Mathlib's `Ideal.ramificationIdx`)
and the residue field extension `κ(P) / κ_A` (Stacks, Remark 15.113.6 (09E8)). Stacks,
Definition 15.113.7 (09E9) calls `L`

1. *unramified with respect to `A`* if every `e(P) = 1` and every `κ(P) / κ_A` is separable;
2. *tamely ramified with respect to `A`* if every `κ(P) / κ_A` is separable and every `e(P)` is
   invertible in `κ_A` (prime to the residue characteristic, or that characteristic is zero);
3. *totally ramified with respect to `A`* if `B` has one maximal ideal `P` and `κ(P) = κ_A`.

Stacks states these for `L` a finite separable extension of the fraction field of `A`. The
definitions below make sense for any field `L` with an `A`-algebra structure; the statements that
need the finite separable setting assume what they use.

## Main definitions

* `TauCeti.Algebra.IsUnramifiedWRT A L`: clause (1) of 09E9.
* `TauCeti.Algebra.IsTamelyRamifiedWRT A L`: clause (2) of 09E9.
* `TauCeti.Algebra.IsTotallyRamifiedWRT A L`: clause (3) of 09E9.

## Main results

* `TauCeti.Algebra.isUnramifiedWRT_iff`, `isTamelyRamifiedWRT_iff`, `isTotallyRamifiedWRT_iff`,
  and the elimination lemmas such as `IsTamelyRamifiedWRT.isUnit_ramificationIdx`.
* `TauCeti.Algebra.IsUnramifiedWRT.isTamelyRamifiedWRT`: unramified extensions are tamely
  ramified.
* `TauCeti.Algebra.IsTotallyRamifiedWRT.isLocalRing`: in a totally ramified extension the
  integral closure is a local ring.
* `TauCeti.Algebra.isTamelyRamifiedWRT_of_charZero`: if the residue field of `A` has
  characteristic zero and the integral closure is Noetherian (as it is for a finite separable
  extension of the fraction field), the extension is tamely ramified.

## References

* [Stacks Project, Definition 15.113.7](https://stacks.math.columbia.edu/tag/09E9) and
  [Remark 15.113.6](https://stacks.math.columbia.edu/tag/09E8).
* Ported in part from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0). `IsTamelyRamifiedWRT` corresponds to
  its `Pcf.Stacks.IsTamelyRamifiedOver` (`lean/Pcf/Stacks/Abhyankar/Scheme/Defs.lean`), which
  asks the condition of `Pcf.Stacks.IsTamelyRamifiedAt`
  (`lean/Pcf/Stacks/Abhyankar/TameRamification.lean`) at every maximal ideal of the integral
  closure, with residue fields of localizations; here the condition is stated on the quotients
  `B ⧸ P` for `P` over the maximal ideal of `A`. The argument of
  `isTamelyRamifiedWRT_of_charZero` is that of `Pcf.Stacks.isTamelyRamifiedAt_of_isUnit_natCast`
  (same file). `IsUnramifiedWRT` and `IsTotallyRamifiedWRT` are new.
-/

public section

universe u

open IsLocalRing

namespace TauCeti.Algebra

variable (A L : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field L] [Algebra A L]

/-- `L` is **unramified with respect to `A`**: every maximal ideal of the integral closure of `A`
in `L` has ramification index one and separable residue field extension. Stacks, Definition
15.113.7 (09E9), clause (1), in the notation of Remark 15.113.6 (09E8). Stacks states it for `L`
a finite separable extension of the fraction field of `A`; the definition makes sense for any
field `L` with an `A`-algebra structure. -/
@[stacks 09E9 "(1)"]
def IsUnramifiedWRT : Prop :=
  ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
    P.ramificationIdx A = 1 ∧
      Algebra.IsSeparable (A ⧸ maximalIdeal A) (integralClosure A L ⧸ P)

/-- `L` is **tamely ramified with respect to `A`**: every residue field extension is separable and
every ramification index is invertible in `κ_A`. Stacks, Definition 15.113.7 (09E9), clause (2). -/
@[stacks 09E9 "(2)"]
def IsTamelyRamifiedWRT : Prop :=
  ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
    Algebra.IsSeparable (A ⧸ maximalIdeal A) (integralClosure A L ⧸ P) ∧
      IsUnit ((P.ramificationIdx A : ℕ) : A ⧸ maximalIdeal A)

/-- `L` is **totally ramified with respect to `A`**: the integral closure has one maximal ideal,
with trivial residue field extension. Stacks, Definition 15.113.7 (09E9), clause (3). -/
@[stacks 09E9 "(3)"]
def IsTotallyRamifiedWRT : Prop :=
  (∃! P : Ideal (integralClosure A L), P.IsMaximal) ∧
    ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
      Module.finrank (A ⧸ maximalIdeal A) (integralClosure A L ⧸ P) = 1

/-- The defining condition of `IsUnramifiedWRT`. -/
theorem isUnramifiedWRT_iff : IsUnramifiedWRT A L ↔
    ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
      P.ramificationIdx A = 1 ∧
        Algebra.IsSeparable (A ⧸ maximalIdeal A) (integralClosure A L ⧸ P) :=
  Iff.rfl

/-- The defining condition of `IsTamelyRamifiedWRT`. -/
theorem isTamelyRamifiedWRT_iff : IsTamelyRamifiedWRT A L ↔
    ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
      Algebra.IsSeparable (A ⧸ maximalIdeal A) (integralClosure A L ⧸ P) ∧
        IsUnit ((P.ramificationIdx A : ℕ) : A ⧸ maximalIdeal A) :=
  Iff.rfl

/-- The defining condition of `IsTotallyRamifiedWRT`. -/
theorem isTotallyRamifiedWRT_iff : IsTotallyRamifiedWRT A L ↔
    (∃! P : Ideal (integralClosure A L), P.IsMaximal) ∧
      ∀ (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)],
        Module.finrank (A ⧸ maximalIdeal A) (integralClosure A L ⧸ P) = 1 :=
  Iff.rfl

variable {A L}

section Elim

variable (P : Ideal (integralClosure A L)) [P.IsMaximal] [P.LiesOver (maximalIdeal A)]

/-- In an unramified extension every ramification index over the maximal ideal is one. -/
theorem IsUnramifiedWRT.ramificationIdx_eq_one (h : IsUnramifiedWRT A L) :
    P.ramificationIdx A = 1 :=
  (h P).1

/-- In an unramified extension every residue field extension is separable. -/
theorem IsUnramifiedWRT.isSeparable (h : IsUnramifiedWRT A L) :
    Algebra.IsSeparable (A ⧸ maximalIdeal A) (integralClosure A L ⧸ P) :=
  (h P).2

/-- In a tamely ramified extension every residue field extension is separable. -/
theorem IsTamelyRamifiedWRT.isSeparable (h : IsTamelyRamifiedWRT A L) :
    Algebra.IsSeparable (A ⧸ maximalIdeal A) (integralClosure A L ⧸ P) :=
  (h P).1

/-- In a tamely ramified extension every ramification index is invertible in `κ_A`. -/
theorem IsTamelyRamifiedWRT.isUnit_ramificationIdx (h : IsTamelyRamifiedWRT A L) :
    IsUnit ((P.ramificationIdx A : ℕ) : A ⧸ maximalIdeal A) :=
  (h P).2

/-- In a totally ramified extension the residue field extension is trivial. -/
theorem IsTotallyRamifiedWRT.finrank_eq_one (h : IsTotallyRamifiedWRT A L) :
    Module.finrank (A ⧸ maximalIdeal A) (integralClosure A L ⧸ P) = 1 :=
  h.2 P

end Elim

/-- In a totally ramified extension the integral closure has exactly one maximal ideal. -/
theorem IsTotallyRamifiedWRT.existsUnique_isMaximal (h : IsTotallyRamifiedWRT A L) :
    ∃! P : Ideal (integralClosure A L), P.IsMaximal :=
  h.1

/-- In a totally ramified extension the integral closure is a local ring. -/
theorem IsTotallyRamifiedWRT.isLocalRing (h : IsTotallyRamifiedWRT A L) :
    IsLocalRing (integralClosure A L) :=
  IsLocalRing.of_unique_max_ideal h.existsUnique_isMaximal

/-- Unramified extensions are tamely ramified. -/
theorem IsUnramifiedWRT.isTamelyRamifiedWRT (h : IsUnramifiedWRT A L) :
    IsTamelyRamifiedWRT A L := fun P _ _ ↦
  ⟨h.isSeparable P, by simp [h.ramificationIdx_eq_one P]⟩

variable (A L) in
/-- If the residue field of `A` has characteristic zero and the integral closure of `A` in `L` is
Noetherian (for instance by `IsIntegralClosure.isNoetherianRing` when `L` is a finite separable
extension of the fraction field of `A`), then `L` is tamely ramified with respect to `A`. -/
theorem isTamelyRamifiedWRT_of_charZero [CharZero (A ⧸ maximalIdeal A)]
    [IsNoetherianRing (integralClosure A L)] : IsTamelyRamifiedWRT A L := fun P _ _ ↦ by
  let : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _
  let : Field (integralClosure A L ⧸ P) := Ideal.Quotient.field P
  have hpos : 0 < P.ramificationIdx A := Ideal.ramificationIdx_pos (R := A) (q := P)
  exact ⟨Algebra.IsAlgebraic.isSeparable_of_perfectField,
    (Nat.cast_ne_zero.mpr hpos.ne').isUnit⟩

end TauCeti.Algebra
