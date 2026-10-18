/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.LTSeries
public import Mathlib.RingTheory.Ideal.Height

/-!
# Height-one primes through an element

In a Noetherian ring, every element of a prime `P` of positive height lies in a prime of height
one contained in `P`. For a Noetherian local ring of positive dimension and `P` the maximal
ideal, this is Stacks, Lemma 58.21.1 (0BJG): every element of the maximal ideal lies in a prime
`𝔭` with `dim A_𝔭 = 1`.

## Main results

* `Ideal.exists_isPrime_le_and_height_eq_one_of_mem`: in a Noetherian ring, an element of a
  prime `P` of positive height lies in a prime of height one contained in `P`.
* `IsLocalRing.exists_isPrime_height_eq_one_of_mem`: in a Noetherian local ring of positive
  dimension, every element of the maximal ideal lies in a prime of height one (Stacks 0BJG).

## References

* [Stacks Project, Lemma 58.21.1](https://stacks.math.columbia.edu/tag/0BJG).
-/

public section

namespace Ideal

variable {R : Type*} [CommRing R]

/-- In a Noetherian ring, every element `f` of a prime `P` of positive height lies in a prime of
height one contained in `P`. This is the general form of Stacks, Lemma 58.21.1 (0BJG). -/
theorem exists_isPrime_le_and_height_eq_one_of_mem [IsNoetherianRing R] {P : Ideal R}
    [P.IsPrime] (hP : 1 ≤ P.height) {f : R} (hf : f ∈ P) :
    ∃ Q : Ideal R, Q.IsPrime ∧ Q ≤ P ∧ f ∈ Q ∧ Q.height = 1 := by
  obtain ⟨chain, hlast, hlength⟩ := P.exists_ltSeries_length_eq_height
  have hpositive : 1 ≤ chain.length := by
    have h : (1 : ℕ∞) ≤ (chain.length : ℕ∞) := by rw [hlength]; exact hP
    exact_mod_cast h
  have hf_last : f ∈ chain.last.asIdeal := by simpa [hlast] using hf
  obtain ⟨adjusted, hf_one, hsame_length, -, hsame_last⟩ :=
    PrimeSpectrum.exist_ltSeries_mem_one_of_mem_last chain hf_last
  have hindex : 1 < adjusted.length + 1 := by omega
  let index : Fin (adjusted.length + 1) := ⟨1, hindex⟩
  have hmaximal : adjusted.length = Order.height adjusted.last := by
    rw [← PrimeSpectrum.height_eq_orderHeight, ← hsame_last, hlast]
    exact (congrArg (fun number : ℕ => (number : ℕ∞)) hsame_length).symm.trans hlength
  have hheight : (adjusted index).asIdeal.height = 1 := by
    rw [PrimeSpectrum.height_eq_orderHeight]
    simpa [index] using Order.height_eq_index_of_length_eq_height_last hmaximal index
  have hbelow : (adjusted index).asIdeal ≤ P := by
    have h : (adjusted index).asIdeal ≤ adjusted.last.asIdeal :=
      (PrimeSpectrum.asIdeal_le_asIdeal (adjusted index) adjusted.last).mpr
        (adjusted.monotone (Fin.le_last _))
    rw [← hsame_last, hlast] at h
    exact h
  have hmem : f ∈ (adjusted index).asIdeal := by
    simpa [index, Fin.one_eq_mk_of_lt hindex] using hf_one
  exact ⟨(adjusted index).asIdeal, inferInstance, hbelow, hmem, hheight⟩

end Ideal

namespace IsLocalRing

variable {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

/-- In a Noetherian local ring of positive dimension, every element of the maximal ideal lies in
a prime of height one. Stacks, Lemma 58.21.1 (0BJG), where `dim A_𝔭 = 1` is `𝔭.height = 1`. -/
@[stacks 0BJG]
theorem exists_isPrime_height_eq_one_of_mem (hA : 1 ≤ ringKrullDim A) {f : A}
    (hf : f ∈ maximalIdeal A) : ∃ p : Ideal A, p.IsPrime ∧ f ∈ p ∧ p.height = 1 := by
  have hm : 1 ≤ (maximalIdeal A).height := by
    rw [← WithBot.coe_le_coe, maximalIdeal_height_eq_ringKrullDim]
    exact_mod_cast hA
  obtain ⟨p, hp, -, hfp, hp1⟩ := Ideal.exists_isPrime_le_and_height_eq_one_of_mem hm hf
  exact ⟨p, hp, hfp, hp1⟩

end IsLocalRing
