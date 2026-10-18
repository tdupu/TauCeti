/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.LTSeries
public import TauCeti.RingTheory.Ideal.Height.Basic

/-!
# Height-one primes through an element

In a Noetherian ring, every element of a prime `P` of positive height lies in a prime of height
one contained in `P`. For a Noetherian local ring of positive dimension and `P` the maximal
ideal, this is Stacks, Lemma 58.21.1 (0BJG): every element of the maximal ideal lies in a prime
`𝔭` with `dim A_𝔭 = 1`.

## Proof

By strong induction on the height of `P`. If it is one, take `P`. Otherwise choose primes
`𝔭₀ < 𝔭₁ < P` with `Ideal.exists_isPrime_lt_and_height_eq`. Mathlib's
`PrimeSpectrum.exist_mem_one_of_mem_two` (Krull's principal ideal theorem in a localization) gives
a prime `Q` with `f ∈ Q` and `𝔭₀ < Q < P`, so `Q` has positive height smaller than that of `P`, and
the induction hypothesis applies to `Q`.

Stacks argues with a minimal prime `𝔮` of `A` with `dim A ⧸ 𝔮 = dim A` and a maximal element among
the non-maximal primes containing `𝔮 + (f)`; the induction above uses a chain below `P` instead.

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
  induction hn : P.height using WellFoundedLT.induction generalizing P with
  | _ n ih =>
  subst hn
  rcases le_or_gt P.height 1 with hP1 | hP2
  · exact ⟨P, inferInstance, le_rfl, hf, le_antisymm hP1 hP⟩
  obtain ⟨𝔭₁, h𝔭₁, h₁P, h𝔭₁ht⟩ :=
    exists_isPrime_lt_and_height_eq (n := 1) (by exact_mod_cast hP2)
  obtain ⟨𝔭₀, h𝔭₀, h₀₁, -⟩ := exists_isPrime_lt_and_height_eq (P := 𝔭₁) (n := 0)
    (by rw [h𝔭₁ht]; norm_num)
  obtain ⟨⟨Q, hQ⟩, hfQ, h₀Q, hQP⟩ := PrimeSpectrum.exist_mem_one_of_mem_two
    (p₀ := ⟨𝔭₀, h𝔭₀⟩) (p₁ := ⟨𝔭₁, h𝔭₁⟩) (p₂ := ⟨P, ‹_›⟩) h₀₁ h₁P hf
  obtain ⟨Q', hQ', hQ'Q, hfQ', hQ'1⟩ := ih Q.height (height_strict_mono_of_isPrime_of_isPrime hQP)
    (le_add_self.trans (height_add_one_le_of_lt_of_isPrime (I := 𝔭₀) h₀Q)) hfQ rfl
  exact ⟨Q', hQ', hQ'Q.trans hQP.le, hfQ', hQ'1⟩

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
