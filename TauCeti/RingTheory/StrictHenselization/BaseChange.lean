/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.StrictHenselization.Neighbourhood
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Base change of pointed étale neighbourhoods

For an `R`-algebra `S`, an `S`-algebra `Ψ` with a compatible `R`-algebra structure and an
`R`-algebra map `φ : Ω → Ψ`, base change `S ⊗[R] _` sends pointed étale neighbourhoods of `R` over
`Ω` to pointed étale neighbourhoods of `S` over `Ψ`. This file defines the functor
`Neighbourhood.baseChange S φ`.

## References

* Stacks Project, Tag 04GW.
* Taylor Dupuy, Thomas Tucker, and Zhuoran Wang, pcfawd-formalization at `9a20b3f`,
  `StrictHenselizationLocalize.lean`.
-/

public section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace TauCeti.StrictHenselization.Neighbourhood

variable {R : Type u} {Ω Ψ : Type v} [CommRing R] [CommRing Ω] [CommRing Ψ] [Algebra R Ω]
  (S : Type u) [CommRing S] [Algebra R S] [Algebra S Ψ] [Algebra R Ψ] [IsScalarTower R S Ψ]
  (φ : Ω →ₐ[R] Ψ)

/-- The point of `S ⊗[R] B` to `Ψ` induced by the point of `B` and the map `φ : Ω → Ψ`. -/
def baseChangePoint (B : Neighbourhood R Ω) : S ⊗[R] B.obj.left →ₐ[S] Ψ :=
  Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId S Ψ) (φ.comp B.point)

/-- The definition of `baseChangePoint`. -/
theorem baseChangePoint_def (B : Neighbourhood R Ω) :
    baseChangePoint S φ B =
      Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId S Ψ) (φ.comp B.point) :=
  (rfl)

/-- The point of `S ⊗[R] B` on a pure tensor. -/
@[simp]
theorem baseChangePoint_tmul (B : Neighbourhood R Ω) (s : S) (b : B.obj.left) :
    baseChangePoint S φ B (s ⊗ₜ[R] b) = algebraMap S Ψ s * φ (B.point b) := by
  simp [baseChangePoint]

/-- The point of `S ⊗[R] B` on the image of a scalar of `R`. -/
@[simp]
theorem baseChangePoint_algebraMap (B : Neighbourhood R Ω) (r : R) :
    baseChangePoint S φ B (algebraMap R (S ⊗[R] B.obj.left) r) = algebraMap R Ψ r :=
  ((baseChangePoint S φ B).restrictScalars R).commutes r

/-- The compatibility of the points of `mk' (S ⊗ B)` and `mk' (S ⊗ C)` with the base-changed map
of a morphism `f : B ⟶ C`; it is the proof obligation used to build `baseChange.map f`. -/
theorem baseChangePoint_comp_map {B C : Neighbourhood R Ω} (f : B ⟶ C) :
    (mk' (S ⊗[R] C.obj.left) (baseChangePoint S φ C)).point.comp
        (Algebra.TensorProduct.map (AlgHom.id S S) f.hom.left.hom) =
      (mk' (S ⊗[R] B.obj.left) (baseChangePoint S φ B)).point := by
  -- `rw [point_mk']` is blocked by the dependent carrier of `mk' …`, so we transport with
  -- `congrArg`.
  refine (congrArg (fun q : S ⊗[R] C.obj.left →ₐ[S] Ψ =>
      q.comp (Algebra.TensorProduct.map (AlgHom.id S S) f.hom.left.hom))
    (point_mk' _ _)).trans (Eq.trans ?_ (point_mk' _ _).symm)
  apply Algebra.TensorProduct.ext'
  intro s b
  simp

-- The objects are spelled `mk' …` because `homMk'_hom_left_hom` only unifies once the carriers are
-- literal.
/-- The underlying algebra map of the morphism of `baseChange`. -/
private theorem homMk'_map_hom_left_hom {B C : Neighbourhood R Ω} (f : B ⟶ C)
    (h : (mk' (S ⊗[R] C.obj.left) (baseChangePoint S φ C)).point.comp
        (Algebra.TensorProduct.map (AlgHom.id S S) f.hom.left.hom) =
      (mk' (S ⊗[R] B.obj.left) (baseChangePoint S φ B)).point) :
    (homMk' (B := mk' (S ⊗[R] B.obj.left) (baseChangePoint S φ B))
      (C := mk' (S ⊗[R] C.obj.left) (baseChangePoint S φ C))
      (Algebra.TensorProduct.map (AlgHom.id S S) f.hom.left.hom) h).hom.left.hom =
      Algebra.TensorProduct.map (AlgHom.id S S) f.hom.left.hom :=
  homMk'_hom_left_hom _ _

/-- Base change along `R → S` and `φ : Ω → Ψ` as a functor from pointed neighbourhoods of `R`
over `Ω` to those of `S` over `Ψ`. -/
-- Exposed so that the carrier of `(baseChange S φ).obj B` is the tensor product.
@[expose] noncomputable def baseChange : Neighbourhood R Ω ⥤ Neighbourhood S Ψ where
  obj B := mk' (S ⊗[R] B.obj.left) (baseChangePoint S φ B)
  map f :=
    homMk' (Algebra.TensorProduct.map (AlgHom.id S S) f.hom.left.hom)
      (baseChangePoint_comp_map S φ f)
  map_id B := by
    apply hom_ext
    rw [homMk'_map_hom_left_hom, id_hom_left_hom]
    exact Algebra.TensorProduct.map_id
  map_comp {B C D} f g := by
    apply hom_ext
    rw [homMk'_map_hom_left_hom, comp_hom_left_hom, comp_hom_left_hom,
      homMk'_map_hom_left_hom, homMk'_map_hom_left_hom]
    exact Algebra.TensorProduct.map_id_comp g.hom.left.hom f.hom.left.hom

/-- The point of the base change of a neighbourhood is `baseChangePoint`. -/
@[simp]
theorem point_baseChange_obj (B : Neighbourhood R Ω) :
    ((baseChange S φ).obj B).point = baseChangePoint S φ B :=
  point_mk' _ _

/-- The underlying algebra map of the base change of a morphism. Not a `simp` lemma, so that
`baseChange_map_tmul` can apply to pure tensors. -/
theorem baseChange_map_hom_left_hom {B C : Neighbourhood R Ω} (f : B ⟶ C) :
    ((baseChange S φ).map f).hom.left.hom =
      Algebra.TensorProduct.map (AlgHom.id S S) f.hom.left.hom :=
  homMk'_map_hom_left_hom S φ f _

/-- The base change of a morphism, on a pure tensor. -/
@[simp]
theorem baseChange_map_tmul {B C : Neighbourhood R Ω} (f : B ⟶ C) (s : S) (b : B.obj.left) :
    ((baseChange S φ).map f).hom.left.hom (s ⊗ₜ[R] b) = s ⊗ₜ[R] f.hom.left.hom b := by
  rw [baseChange_map_hom_left_hom]
  exact Algebra.TensorProduct.map_tmul (AlgHom.id S S) f.hom.left.hom s b

end TauCeti.StrictHenselization.Neighbourhood
