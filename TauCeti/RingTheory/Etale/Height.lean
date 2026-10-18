/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Unramified.LocalStructure
public import TauCeti.RingTheory.KrullDimension.Fiber

/-!
# Étale homomorphisms preserve heights

An étale algebra is flat, hence satisfies going down, and quasi-finite, so
`Ideal.height_eq_height_under_of_quasiFinite` applies: every prime has the height of the prime
below it.

## Main results

* `Ideal.height_eq_height_under_of_etale`: étale homomorphisms of Noetherian rings preserve
  heights.

## References

* [Stacks Project, Tag 00ON](https://stacks.math.columbia.edu/tag/00ON)
* Ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0):
  `Pcf.Stacks.height_eq_height_under_of_etale` in `lean/Pcf/Stacks/Common/EtaleNormal.lean`.
-/

public section

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Étale homomorphisms of Noetherian rings preserve heights. -/
theorem height_eq_height_under_of_etale [IsNoetherianRing R] [Algebra.Etale R S]
    (P : Ideal S) [P.IsPrime] : P.height = (P.under R).height :=
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  height_eq_height_under_of_quasiFinite P

end Ideal
