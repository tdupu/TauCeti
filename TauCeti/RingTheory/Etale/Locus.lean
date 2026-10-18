/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Smooth.Fiber

/-!
# Étale at a prime from flat and unramified at that prime

Mathlib's `Algebra.Etale.of_formallyUnramified_of_flat` (Stacks 08WD) and
`Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat` assume that the whole algebra is flat. This file
proves the pointwise statement: a finitely presented `R`-algebra `S` that is flat and unramified
at a prime `𝔮` (that is, `S_𝔮` is flat and formally unramified over `R`) is étale at `𝔮`.

The proof goes through local rings. A flat, formally unramified local homomorphism `R → S` that is
a localization of a finitely presented `R`-algebra is formally étale: its closed fibre is formally
unramified and essentially of finite type over the residue field, hence formally étale, and
`Algebra.FormallySmooth.of_formallySmooth_residueField_tensor` lifts formal smoothness from the
closed fibre. With `𝔭 = 𝔮 ∩ R`, this applies to `R_𝔭 → S_𝔮`, and composing with the formally
étale `R → R_𝔭` gives the statement.

## Main results

* `Algebra.FormallyEtale.of_formallyUnramified_of_flat_of_isLocalization`: a flat, formally
  unramified local homomorphism that is a localization of a finitely presented algebra is formally
  étale.
* `Algebra.IsEtaleAt.of_isUnramifiedAt_of_flatAt`: a finitely presented algebra that is flat and
  unramified at a prime is étale at it.

## References

* [Stacks Project, Lemma 10.151.8](https://stacks.math.columbia.edu/tag/08WD).
* Ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0):
  `Algebra.FormallyEtale.of_formallyUnramified_of_flat_of_isLocalization` is
  `Pcf.Stacks.formallyEtale_of_flat_of_formallyUnramified_of_isLocalization` in
  `lean/Pcf/Stacks/Purity/LocalEtale.lean`, and `Algebra.IsEtaleAt.of_isUnramifiedAt_of_flatAt` is
  `Pcf.Stacks.isEtaleAt_of_flat_of_formallyUnramified` in
  `lean/Pcf/Stacks/Purity/Tag0BMBLocalModel.lean`. The localization set-up in the latter is
  adapted from Mathlib's `Algebra.IsSmoothAt.of_formallySmooth_fiber`
  (`Mathlib/RingTheory/Smooth/Fiber.lean`).
-/

public section

namespace Algebra

open IsLocalRing

/-- A flat, formally unramified local homomorphism `R → S`, where `S` is a localization of a
finitely presented `R`-algebra `P`, is formally étale. This is a local form of
`Algebra.Etale.of_formallyUnramified_of_flat`. -/
theorem FormallyEtale.of_formallyUnramified_of_flat_of_isLocalization
    {R S P : Type*} [CommRing R] [CommRing S] [CommRing P]
    [Algebra R S] [Algebra R P] [Algebra P S] [IsScalarTower R P S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [FormallyUnramified R S] [Module.Flat R S]
    (M : Submonoid P) [IsLocalization M S] [FinitePresentation R P] :
    FormallyEtale R S := by
  have : EssFiniteType P S := .of_isLocalization S M
  have : EssFiniteType R S := .comp R P S
  have : FormallyEtale (ResidueField R) (TensorProduct R (ResidueField R) S) :=
    .of_formallyUnramified_of_field _ _
  have : FormallySmooth R S := .of_formallySmooth_residueField_tensor (P := P) M
  exact .of_formallyUnramified_and_formallySmooth

/-- A finitely presented `R`-algebra `S` that is flat and unramified at a prime `q`, meaning that
`S_q` is flat and formally unramified over `R`, is étale at `q`. Unlike
`Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat`, flatness is only assumed at `q`. -/
theorem IsEtaleAt.of_isUnramifiedAt_of_flatAt {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [FinitePresentation R S] (q : Ideal S) [q.IsPrime]
    [Module.Flat R (Localization.AtPrime q)] [IsUnramifiedAt R q] :
    IsEtaleAt R q := by
  let p : Ideal R := q.under R
  have : q.LiesOver p := ⟨rfl⟩
  let Rp := Localization.AtPrime p
  let Sp := Localization (algebraMapSubmonoid S p.primeCompl)
  let Sq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  let f : Sp →ₐ[S] Sq := IsLocalization.liftAlgHom (M := algebraMapSubmonoid S p.primeCompl)
      (f := Algebra.ofId _ _) (by
    rintro ⟨_, x, hx, rfl⟩
    simpa using! IsLocalization.map_units (M := q.primeCompl) Sq ⟨algebraMap _ _ x,
      by simp_all [q.over_def p]⟩)
  algebraize [f.toRingHom]
  have : IsScalarTower R Sp Sq := .to₁₃₄ _ S _ _
  have : IsScalarTower Rp Sp Sq := .of_algebraMap_eq' <| by
    apply IsLocalization.ringHom_ext p.primeCompl
    simp only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  have : IsLocalization (algebraMapSubmonoid Sp q.primeCompl) Sq :=
    .isLocalization_of_submonoid_le _ _ (algebraMapSubmonoid S p.primeCompl) _
    (by rintro _ ⟨x, hx, rfl⟩; simp_all [q.over_def p])
  have : FinitePresentation Rp Sp := by
    have : IsPushout R Rp S Sp := .symm <| isPushout_of_isLocalization p.primeCompl _ _ _
    exact .equiv (IsPushout.equiv R Rp S Sp)
  have : Module.Flat Rp Sq := (Module.flat_iff_of_isLocalization Rp p.primeCompl Sq).mpr ‹_›
  have : FormallyEtale Rp Sq :=
    .of_formallyUnramified_of_flat_of_isLocalization (algebraMapSubmonoid Sp q.primeCompl)
  exact FormallyEtale.comp R Rp Sq

end Algebra
