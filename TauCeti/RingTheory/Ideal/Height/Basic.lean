/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Ideal.Height

/-!
# Primes of prescribed height

Below a prime ideal `P` of finite height, every smaller height is attained by a prime strictly
contained in `P`. This is Mathlib's order-theoretic `Order.coe_lt_height_iff` read on the prime
spectrum.

## Main results

* `Ideal.exists_isPrime_lt_and_height_eq`: below a prime `P` of finite height greater than `n`
  there is a prime of height `n`.
-/

public section

namespace Ideal

variable {R : Type*} [CommRing R]

/-- Below a prime `P` of finite height greater than `n` there is a prime of height `n`. -/
theorem exists_isPrime_lt_and_height_eq {P : Ideal R} [P.IsPrime] [P.FiniteHeight]
    {n : ℕ} (h : n < P.height) : ∃ Q : Ideal R, Q.IsPrime ∧ Q < P ∧ Q.height = n := by
  let p : PrimeSpectrum R := ⟨P, inferInstance⟩
  have hp : p.asIdeal.height = Order.height p := PrimeSpectrum.height_eq_orderHeight p
  have hfin : Order.height p < ⊤ := hp ▸ height_lt_top_of_isPrime
  obtain ⟨q, hqp, hq⟩ := (Order.coe_lt_height_iff hfin).mp (hp ▸ h)
  exact ⟨q.asIdeal, inferInstance, hqp, (PrimeSpectrum.height_eq_orderHeight q).trans hq⟩

end Ideal
