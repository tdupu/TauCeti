/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Heights along flat quasi-finite homomorphisms

Let `R → S` be a homomorphism of Noetherian rings and `𝔮` a prime of `S` at which `S` is flat and
quasi-finite over `R`: `Localization.AtPrime 𝔮` is flat over `R` and `Algebra.QuasiFiniteAt R 𝔮`.
Then `𝔮` and its contraction `𝔭 = 𝔮 ∩ R` have the same height. This is the dimension formula
`ht 𝔮 = ht 𝔭 + dim (S_𝔮 ⧸ 𝔭 S_𝔮)` (Stacks 00ON, Mathlib's
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`, which needs going down, here supplied by
flatness) with a fibre of dimension zero.

The formula is applied to `R → S_𝔮` and its maximal ideal, so only flatness at `𝔮` is needed. In
the quasi-finite `R`-algebra `S_𝔮`, a prime contained in the maximal ideal and with the same
contraction is the maximal ideal itself (`Algebra.QuasiFinite.eq_of_le_of_under_eq`), so the
maximal ideal is a minimal prime over the extension of `𝔭` and the fibre term vanishes.

## Main results

* `Ideal.height_eq_height_under_of_flat_of_quasiFiniteAt`: heights are preserved at a prime where
  the homomorphism is flat and quasi-finite.
* `Ideal.height_eq_height_under_of_etale`: étale homomorphisms preserve heights.
* `Ideal.height_eq_height_under_of_finite_of_flat`: finite flat homomorphisms preserve heights.

## References

* [Stacks Project, Lemma 10.112.7](https://stacks.math.columbia.edu/tag/00ON).
* Ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0):
  `lean/Pcf/Stacks/Common/EtaleNormal.lean`, whose
  `Pcf.Stacks.height_eq_height_under_of_flat_of_quasiFiniteAt` assumes `S` flat over `R` (the
  private `height_eq_height_under_of_flat_of_quasiFinite` here is its proof, and the statement
  with flatness only at `𝔮` is new) and whose `Pcf.Stacks.height_eq_height_under_of_etale` is
  `Ideal.height_eq_height_under_of_etale`; and
  `lean/Pcf/Stacks/Purity/HeightOneEtaleBridge.lean`, whose
  `Ideal.height_under_eq_of_finite_of_flat` is `Ideal.height_eq_height_under_of_finite_of_flat`
  (with the sides swapped), now a corollary.
-/

public section

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- For a flat quasi-finite algebra over a Noetherian ring with Noetherian total ring, every prime
has the height of its contraction. -/
private theorem height_eq_height_under_of_flat_of_quasiFinite [IsNoetherianRing R]
    [IsNoetherianRing S] [Module.Flat R S] [Algebra.QuasiFinite R S] (P : Ideal S) [P.IsPrime] :
    P.height = (P.under R).height := by
  let p := P.under R
  have : P.LiesOver p := ⟨rfl⟩
  let I := p.map (algebraMap R S)
  have hIP : I ≤ P := map_comap_le
  have hker : RingHom.ker (Quotient.mk I) ≤ P := by rwa [mk_ker]
  have hq : (P.map (Quotient.mk I)).IsPrime := map_isPrime_of_surjective Quotient.mk_surjective hker
  have hcomap : (P.map (Quotient.mk I)).comap (Quotient.mk I) = P := by
    rw [comap_map_of_surjective _ Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, mk_ker,
      sup_eq_left.mpr hIP]
  have hmin : P.map (Quotient.mk I) ∈ minimalPrimes (S ⧸ I) := by
    refine ⟨⟨hq, bot_le⟩, fun r ⟨hr, _⟩ hrq ↦ ?_⟩
    let r' := r.comap (Quotient.mk I)
    have hr'P : r' ≤ P := hcomap ▸ comap_mono hrq
    have hIr' : I ≤ r' := by
      intro x hx
      change Quotient.mk I x ∈ r
      rw [Quotient.eq_zero_iff_mem.mpr hx]
      exact r.zero_mem
    have hunder : r'.under R = P.under R :=
      le_antisymm (comap_mono hr'P) (le_comap_of_map_le hIr' : p ≤ r'.under R)
    have heq : r' = P := Algebra.QuasiFinite.eq_of_le_of_under_eq r' P hr'P hunder
    rw [← heq, map_comap_of_surjective _ Quotient.mk_surjective]
  rw [height_eq_height_add_of_liesOver_of_hasGoingDown p P, height_eq_zero_iff.mpr hmin, add_zero]

/-- Heights are preserved at a prime where a homomorphism of Noetherian rings is flat and
quasi-finite: the dimension formula (Stacks 00ON) with a zero-dimensional fibre. -/
theorem height_eq_height_under_of_flat_of_quasiFiniteAt [IsNoetherianRing R] [IsNoetherianRing S]
    (q : Ideal S) [q.IsPrime] [Algebra.QuasiFiniteAt R q]
    [Module.Flat R (Localization.AtPrime q)] : q.height = (q.under R).height := by
  let m := IsLocalRing.maximalIdeal (Localization.AtPrime q)
  have hm : m.under S = q := Localization.AtPrime.under_maximalIdeal
  have hheight : m.height = q.height := by
    rw [← IsLocalization.height_under q.primeCompl m, hm]
  have hunder : m.under R = q.under R := by
    rw [← under_under (B := S), hm]
  rw [← hheight, ← hunder]
  exact height_eq_height_under_of_flat_of_quasiFinite m

/-- Étale homomorphisms of Noetherian rings preserve heights. -/
theorem height_eq_height_under_of_etale [IsNoetherianRing R] [Algebra.Etale R S]
    (q : Ideal S) [q.IsPrime] : q.height = (q.under R).height := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  have : Module.Flat R (Localization.AtPrime q) := Module.Flat.trans R S _
  exact height_eq_height_under_of_flat_of_quasiFiniteAt q

/-- Finite flat homomorphisms of Noetherian rings preserve heights. -/
theorem height_eq_height_under_of_finite_of_flat [IsNoetherianRing R] [Module.Finite R S]
    [Module.Flat R S] (q : Ideal S) [q.IsPrime] : q.height = (q.under R).height := by
  have : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  have : Module.Flat R (Localization.AtPrime q) := Module.Flat.trans R S _
  exact height_eq_height_under_of_flat_of_quasiFiniteAt q

end Ideal
