/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Unramified.Locus

/-!
# Unramifiedness at a prime along a base change

Let `S` and `R'` be `R`-algebras, `𝔮` a prime of `S` and `𝔔` a prime of `R' ⊗[R] S` lying over
`𝔮`. If `S` is unramified over `R` at `𝔮`, then `R' ⊗[R] S` is unramified over `R'` at `𝔔`.

The base change `R' ⊗[R] S_𝔮` is formally unramified over `R'`
(`Algebra.FormallyUnramified.base_change`), and `(R' ⊗[R] S)_𝔔` is formally unramified over it,
since over `R' ⊗[R] S` it is a localization. The map `S_𝔮 → (R' ⊗[R] S)_𝔔` is built as in
Mathlib's `Algebra.IsUnramifiedAt.residueField`.

## Main results

* `Algebra.IsUnramifiedAt.baseChange`: unramifiedness at a prime ascends along any base change.
-/

public section

open TensorProduct

namespace Algebra

variable {R R' S : Type*} [CommRing R] [CommRing R'] [CommRing S] [Algebra R R'] [Algebra R S]

/-- Unramifiedness at a prime ascends along any base change: if `S` is unramified over `R` at `q`
and `Q` is a prime of `R' ⊗[R] S` lying over `q`, then `R' ⊗[R] S` is unramified over `R'` at
`Q`. -/
theorem IsUnramifiedAt.baseChange (q : Ideal S) [q.IsPrime] (Q : Ideal (R' ⊗[R] S)) [Q.IsPrime]
    (hQ : Q.comap Algebra.TensorProduct.includeRight.toRingHom = q) [IsUnramifiedAt R q] :
    IsUnramifiedAt R' Q := by
  let T := R' ⊗[R] S
  let Sq := Localization.AtPrime q
  let TQ := Localization.AtPrime Q
  -- `R' ⊗[R] S_q` is formally unramified over `R'` and maps to `T_Q`
  let f₀ : Sq →ₐ[R] TQ := Localization.localAlgHom q Q
    (Algebra.TensorProduct.includeRight (R := R) (A := R')) hQ.symm
  let f : R' ⊗[R] Sq →ₐ[R'] TQ :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) f₀ fun _ _ ↦ .all _ _
  let g : T →ₐ[R'] R' ⊗[R] Sq :=
    Algebra.TensorProduct.map (.id _ _) (IsScalarTower.toAlgHom _ _ _)
  have hf₀ (s : S) : f₀ (algebraMap S Sq s) = algebraMap T TQ (1 ⊗ₜ s) :=
    Localization.localRingHom_to_map _ _ _ hQ.symm s
  have hfg (x : T) : f (g x) = algebraMap T TQ x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r s =>
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply,
        IsScalarTower.coe_toAlgHom', hf₀, Algebra.ofId_apply,
        IsScalarTower.algebraMap_apply R' T TQ, ← map_mul, Algebra.TensorProduct.algebraMap_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, Algebra.algebraMap_self,
        RingHom.id_apply]
  algebraize [f.toRingHom, g.toRingHom]
  have : IsScalarTower T (R' ⊗[R] Sq) TQ := .of_algebraMap_eq fun x ↦ (hfg x).symm
  have : FormallyUnramified T TQ := .of_isLocalization Q.primeCompl
  have : FormallyUnramified (R' ⊗[R] Sq) TQ := .of_restrictScalars T _ _
  exact FormallyUnramified.comp R' (R' ⊗[R] Sq) TQ

end Algebra
