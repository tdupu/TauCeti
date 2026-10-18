/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Preorder.Finite
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.ZMod.Defs

/-!
# Preperiodic points and forward orbits

A point `x` is *preperiodic* for a self-map `f` if some iterate `f^[r] x` is periodic, that is,
`f^[r + s] x = f^[r] x` for some `r` and some `s ≥ 1`. Equivalently, the forward orbit of `x` is
finite. The *forward orbit* of a set `s` is `⋃ n, f^[n] '' s`; for a finite set it is finite exactly
when every point of `s` is preperiodic. These are the notions behind postcritically finite maps:
a map is postcritically finite when the forward orbit of its branch locus is finite.

## Main definitions

* `Function.IsPreperiodicPt f x`: `f^[r + s] x = f^[r] x` for some `r` and some `s > 0`.
* `Function.forwardOrbit f s`: the forward orbit `⋃ n, f^[n] '' s` of a set `s`.

## Main results

* `Function.isPreperiodicPt_iff_finite_range_iterate`: a point is preperiodic iff its forward
  orbit `Set.range (f^[·] x)` is finite.
* `Function.IsPreperiodicPt.exists_isPeriodicPt_iterate`: some iterate of a preperiodic point is
  periodic.
* `Function.finite_forwardOrbit_iff`: the forward orbit of a finite set is finite iff every point of
  the set is preperiodic.
* `Function.forwardOrbit_iterate`: for `m > 0`, the forward orbit of `⋃ i < m, f^[i] '' s` under
  `f^[m]` is the forward orbit of `s` under `f`.
* `Function.exists_isPeriodicPt_of_mapsTo`: a self-map of a finite nonempty invariant set has a
  periodic point in it.
* `Function.Semiconj.image_forwardOrbit` and
  `Function.Semiconj.finite_forwardOrbit_iff_of_finite_fibers`: a semiconjugacy carries forward
  orbits to forward orbits, and with finite fibres it preserves their finiteness.

## References

* Ported in part from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0), `lean/Pcf/Dynamics.lean`, where the
  same arguments are made for the postcritical set of an abstract divisor dynamics:
  `forwardOrbit_eq_biUnion_range_iterate` is its
  `Pcf.DivisorDynamics.postcriticalSet_eq_biUnion_orbit`, `finite_forwardOrbit_iff` its
  `Pcf.DivisorDynamics.isPCF_iff_forall_orbit_finite`,
  `forwardOrbit_iterate` its `Pcf.DivisorDynamics.postcriticalSet_iterate`, and the finite-fibre
  direction of `Semiconj.finite_forwardOrbit_iff_of_finite_fibers` its
  `Pcf.DivisorDynamics.isPCF_of_finite_cover`. The notion of a preperiodic point is new here.
-/

public section

namespace Function

open Set

variable {α β : Type*} {f : α → α} {x : α}

/-! ### Preperiodic points -/

/-- `x` is **preperiodic** for `f`: `f^[r + s] x = f^[r] x` for some `r` and some `s ≥ 1`. -/
def IsPreperiodicPt (f : α → α) (x : α) : Prop :=
  ∃ r s : ℕ, 0 < s ∧ f^[r + s] x = f^[r] x

/-- The defining property of a preperiodic point. -/
theorem isPreperiodicPt_iff : IsPreperiodicPt f x ↔ ∃ r s : ℕ, 0 < s ∧ f^[r + s] x = f^[r] x :=
  Iff.rfl

/-- The equation `f^[r + s] x = f^[r] x` says that `f^[r] x` is periodic of period `s`. -/
theorem iterate_add_eq_iterate_iff_isPeriodicPt {r s : ℕ} :
    f^[r + s] x = f^[r] x ↔ IsPeriodicPt f s (f^[r] x) := by
  rw [add_comm, iterate_add_apply, IsPeriodicPt, IsFixedPt]

/-- A point some iterate of which is periodic of positive period is preperiodic. -/
theorem IsPreperiodicPt.of_isPeriodicPt_iterate {r n : ℕ} (hn : 0 < n)
    (h : IsPeriodicPt f n (f^[r] x)) : IsPreperiodicPt f x :=
  ⟨r, n, hn, iterate_add_eq_iterate_iff_isPeriodicPt.mpr h⟩

/-- Some iterate of a preperiodic point is periodic. -/
theorem IsPreperiodicPt.exists_isPeriodicPt_iterate (hx : IsPreperiodicPt f x) :
    ∃ r n, 0 < n ∧ IsPeriodicPt f n (f^[r] x) := by
  obtain ⟨r, s, hs, hrs⟩ := hx
  exact ⟨r, s, hs, iterate_add_eq_iterate_iff_isPeriodicPt.mp hrs⟩

/-- A periodic point of positive period is preperiodic. -/
theorem IsPeriodicPt.isPreperiodicPt {n : ℕ} (hn : 0 < n) (hx : IsPeriodicPt f n x) :
    IsPreperiodicPt f x :=
  IsPreperiodicPt.of_isPeriodicPt_iterate (r := 0) hn hx

/-- Every point of `periodicPts f` is preperiodic. -/
theorem isPreperiodicPt_of_mem_periodicPts (hx : x ∈ periodicPts f) : IsPreperiodicPt f x :=
  let ⟨_, hn, hper⟩ := mem_periodicPts.mp hx
  hper.isPreperiodicPt hn

/-- Iterates of a preperiodic point are preperiodic. -/
theorem IsPreperiodicPt.apply_iterate (hx : IsPreperiodicPt f x) (m : ℕ) :
    IsPreperiodicPt f (f^[m] x) := by
  obtain ⟨r, n, hn, hper⟩ := hx.exists_isPeriodicPt_iterate
  refine IsPreperiodicPt.of_isPeriodicPt_iterate (r := r) hn ?_
  rw [(Commute.iterate_iterate_self f r m).eq x]
  exact hper.apply_iterate m

/-- The image of a preperiodic point is preperiodic. -/
theorem IsPreperiodicPt.apply (hx : IsPreperiodicPt f x) : IsPreperiodicPt f (f x) :=
  hx.apply_iterate 1

/-- A point is preperiodic iff any of its iterates is. -/
@[simp]
theorem isPreperiodicPt_apply_iterate_iff (m : ℕ) :
    IsPreperiodicPt f (f^[m] x) ↔ IsPreperiodicPt f x := by
  refine ⟨fun ⟨r, s, hs, hrs⟩ ↦ ⟨r + m, s, hs, ?_⟩, fun hx ↦ hx.apply_iterate m⟩
  rwa [add_right_comm, iterate_add_apply, iterate_add_apply f r m]

/-- A point is preperiodic iff its image is. -/
@[simp]
theorem isPreperiodicPt_apply_iff : IsPreperiodicPt f (f x) ↔ IsPreperiodicPt f x :=
  isPreperiodicPt_apply_iterate_iff 1

/-- **Preperiodic points have finite forward orbits**, and conversely. -/
theorem isPreperiodicPt_iff_finite_range_iterate :
    IsPreperiodicPt f x ↔ (Set.range fun n : ℕ ↦ f^[n] x).Finite := by
  constructor
  · intro hx
    obtain ⟨r, s, hs, hper⟩ := hx.exists_isPeriodicPt_iterate
    refine ((Set.finite_Iio (r + s)).image fun n ↦ f^[n] x).subset ?_
    rintro _ ⟨n, rfl⟩
    rcases lt_or_ge n r with hn | hn
    · exact ⟨n, by simp only [Set.mem_Iio]; omega, rfl⟩
    · refine ⟨(n - r) % s + r, ?_, ?_⟩
      · have := Nat.mod_lt (n - r) hs
        simp only [Set.mem_Iio]
        omega
      · have hnr : n = (n - r) + r := by omega
        dsimp only
        rw [iterate_add_apply, hper.iterate_mod_apply, ← iterate_add_apply, ← hnr]
  · intro hfin
    obtain ⟨m, n, hmn, heq⟩ :=
      hfin.exists_lt_map_eq_of_forall_mem (f := fun n : ℕ ↦ f^[n] x) (Set.mem_range_self ·)
    exact ⟨m, n - m, by omega, by rw [Nat.add_sub_cancel' hmn.le]; exact heq.symm⟩

/-- A preperiodic point of `f` is preperiodic for every iterate of `f`. -/
theorem IsPreperiodicPt.iterate (hx : IsPreperiodicPt f x) (m : ℕ) :
    IsPreperiodicPt f^[m] x := by
  rw [isPreperiodicPt_iff_finite_range_iterate] at hx ⊢
  refine hx.subset ?_
  rintro _ ⟨n, rfl⟩
  exact ⟨m * n, by simp only [iterate_mul]⟩

/-- For `m > 0`, a point is preperiodic for `f^[m]` iff it is preperiodic for `f`. -/
theorem isPreperiodicPt_iterate_iff {m : ℕ} (hm : 0 < m) :
    IsPreperiodicPt f^[m] x ↔ IsPreperiodicPt f x := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ hx.iterate m⟩
  rw [isPreperiodicPt_iff_finite_range_iterate] at hx ⊢
  refine ((Set.finite_lt_nat m).biUnion fun i _ ↦ hx.image f^[i]).subset ?_
  rintro _ ⟨N, rfl⟩
  refine Set.mem_biUnion (Nat.mod_lt N hm) ⟨_, ⟨N / m, rfl⟩, ?_⟩
  dsimp only
  rw [← iterate_mul, ← iterate_add_apply, Nat.mod_add_div N m]

/-- A semiconjugacy carries preperiodic points to preperiodic points. -/
protected theorem IsPreperiodicPt.map {g : β → β} {π : β → α} (h : Semiconj π g f) {y : β}
    (hy : IsPreperiodicPt g y) : IsPreperiodicPt f (π y) := by
  obtain ⟨r, s, hs, hrs⟩ := hy
  refine ⟨r, s, hs, ?_⟩
  rw [← (h.iterate_right (r + s)).eq, ← (h.iterate_right r).eq, hrs]

/-! ### Forward orbits of sets -/

/-- The **forward orbit** `⋃ n, f^[n] '' s` of a set `s` under `f`. -/
def forwardOrbit (f : α → α) (s : Set α) : Set α :=
  ⋃ n : ℕ, f^[n] '' s

variable {s t : Set α}

/-- The defining formula of the forward orbit. -/
theorem forwardOrbit_def : forwardOrbit f s = ⋃ n : ℕ, f^[n] '' s := by
  rw [forwardOrbit]

@[simp]
theorem mem_forwardOrbit {y : α} : y ∈ forwardOrbit f s ↔ ∃ n, ∃ x ∈ s, f^[n] x = y := by
  simp [forwardOrbit]

theorem subset_forwardOrbit : s ⊆ forwardOrbit f s :=
  fun x hx ↦ mem_forwardOrbit.mpr ⟨0, x, hx, rfl⟩

theorem iterate_mem_forwardOrbit (hx : x ∈ s) (n : ℕ) : f^[n] x ∈ forwardOrbit f s :=
  mem_forwardOrbit.mpr ⟨n, x, hx, rfl⟩

/-- The forward orbit is forward invariant. -/
theorem mapsTo_forwardOrbit : MapsTo f (forwardOrbit f s) (forwardOrbit f s) := by
  intro y hy
  obtain ⟨n, x, hx, rfl⟩ := mem_forwardOrbit.mp hy
  rw [← iterate_succ_apply' f n x]
  exact iterate_mem_forwardOrbit hx (n + 1)

/-- The forward orbit of `s` is the smallest forward-invariant set containing `s`. -/
theorem forwardOrbit_subset_of_mapsTo (hst : s ⊆ t) (ht : MapsTo f t t) :
    forwardOrbit f s ⊆ t := by
  intro y hy
  obtain ⟨n, x, hx, rfl⟩ := mem_forwardOrbit.mp hy
  exact ht.iterate n (hst hx)

/-- A forward-invariant set contains the forward orbit of `s` iff it contains `s`. -/
theorem forwardOrbit_subset_iff (ht : MapsTo f t t) : forwardOrbit f s ⊆ t ↔ s ⊆ t :=
  ⟨subset_forwardOrbit.trans, fun hst ↦ forwardOrbit_subset_of_mapsTo hst ht⟩

/-- A set is its own forward orbit iff it is forward invariant. -/
theorem forwardOrbit_eq_self_iff : forwardOrbit f s = s ↔ MapsTo f s s :=
  ⟨fun h ↦ h ▸ mapsTo_forwardOrbit, fun h ↦
    (forwardOrbit_subset_of_mapsTo subset_rfl h).antisymm subset_forwardOrbit⟩

@[simp]
theorem forwardOrbit_forwardOrbit : forwardOrbit f (forwardOrbit f s) = forwardOrbit f s :=
  forwardOrbit_eq_self_iff.mpr mapsTo_forwardOrbit

@[gcongr]
theorem forwardOrbit_mono (hst : s ⊆ t) : forwardOrbit f s ⊆ forwardOrbit f t :=
  forwardOrbit_subset_of_mapsTo (hst.trans subset_forwardOrbit) mapsTo_forwardOrbit

@[simp]
theorem forwardOrbit_empty : forwardOrbit f ∅ = ∅ := by
  simp [forwardOrbit]

@[simp]
theorem forwardOrbit_union : forwardOrbit f (s ∪ t) = forwardOrbit f s ∪ forwardOrbit f t := by
  simp only [forwardOrbit, image_union, iUnion_union_distrib]

/-- The forward orbit of the image of `s` is contained in the forward orbit of `s`. -/
theorem forwardOrbit_image_subset : forwardOrbit f (f '' s) ⊆ forwardOrbit f s :=
  forwardOrbit_subset_of_mapsTo (mapsTo_forwardOrbit.mono_left subset_forwardOrbit).image_subset
    mapsTo_forwardOrbit

/-- The forward orbit of a set is the union of the forward orbits of its points. -/
theorem forwardOrbit_eq_biUnion_range_iterate :
    forwardOrbit f s = ⋃ x ∈ s, Set.range fun n : ℕ ↦ f^[n] x := by
  ext y
  simp only [mem_forwardOrbit, mem_iUnion, mem_range, exists_prop]
  tauto

@[simp]
theorem forwardOrbit_singleton : forwardOrbit f {x} = Set.range fun n : ℕ ↦ f^[n] x := by
  simp [forwardOrbit_eq_biUnion_range_iterate]

/-- Every point of a set with finite forward orbit is preperiodic. -/
theorem IsPreperiodicPt.of_finite_forwardOrbit (h : (forwardOrbit f s).Finite) (hx : x ∈ s) :
    IsPreperiodicPt f x :=
  isPreperiodicPt_iff_finite_range_iterate.mpr
    (h.subset (by rw [← forwardOrbit_singleton]; exact forwardOrbit_mono (by simpa)))

/-- **The forward orbit of a finite set is finite iff each of its points is preperiodic.** -/
theorem finite_forwardOrbit_iff (hs : s.Finite) :
    (forwardOrbit f s).Finite ↔ ∀ x ∈ s, IsPreperiodicPt f x := by
  refine ⟨fun h _ hx ↦ .of_finite_forwardOrbit h hx, fun h ↦ ?_⟩
  rw [forwardOrbit_eq_biUnion_range_iterate]
  exact hs.biUnion fun x hx ↦ isPreperiodicPt_iff_finite_range_iterate.mp (h x hx)

/-- For `m > 0`, the forward orbit of `⋃ i < m, f^[i] '' s` under `f^[m]` is the forward orbit of
`s` under `f`. -/
theorem forwardOrbit_iterate {m : ℕ} (hm : 0 < m) :
    forwardOrbit f^[m] (⋃ i < m, f^[i] '' s) = forwardOrbit f s := by
  ext y
  simp only [mem_forwardOrbit, mem_iUnion, mem_image, exists_prop]
  constructor
  · rintro ⟨j, _, ⟨i, -, x, hx, rfl⟩, rfl⟩
    exact ⟨m * j + i, x, hx, by rw [iterate_add_apply, iterate_mul]⟩
  · rintro ⟨N, x, hx, rfl⟩
    refine ⟨N / m, f^[N % m] x, ⟨N % m, Nat.mod_lt N hm, x, hx, rfl⟩, ?_⟩
    rw [← iterate_mul, ← iterate_add_apply, Nat.div_add_mod]

/-- A self-map of a finite nonempty invariant set has a periodic point in it. -/
theorem exists_isPeriodicPt_of_mapsTo (hs : s.Finite) (hne : s.Nonempty) (h : MapsTo f s s) :
    ∃ x ∈ s, ∃ n, 0 < n ∧ IsPeriodicPt f n x := by
  obtain ⟨y, hy⟩ := hne
  have hfin : (Set.range fun n : ℕ ↦ f^[n] y).Finite :=
    hs.subset (by rintro _ ⟨n, rfl⟩; exact h.iterate n hy)
  obtain ⟨r, n, hn, hper⟩ :=
    (isPreperiodicPt_iff_finite_range_iterate.mpr hfin).exists_isPeriodicPt_iterate
  exact ⟨f^[r] y, h.iterate r hy, n, hn, hper⟩

/-! ### Semiconjugacies -/

/-- A semiconjugacy `π ∘ g = f ∘ π` carries forward orbits under `g` to forward orbits under `f`.
-/
theorem Semiconj.image_forwardOrbit {g : β → β} {π : β → α} (h : Semiconj π g f) (t : Set β) :
    π '' forwardOrbit g t = forwardOrbit f (π '' t) := by
  simp only [forwardOrbit, image_iUnion, image_image, (h.iterate_right _).eq]

/-- Along a semiconjugacy with finite fibres, the forward orbit of `t` is finite iff the forward
orbit of its image is. -/
theorem Semiconj.finite_forwardOrbit_iff_of_finite_fibers {g : β → β} {π : β → α}
    (h : Semiconj π g f) (hfib : ∀ a, (π ⁻¹' {a}).Finite) (t : Set β) :
    (forwardOrbit g t).Finite ↔ (forwardOrbit f (π '' t)).Finite := by
  rw [← h.image_forwardOrbit]
  refine ⟨fun hfin ↦ hfin.image π, fun hfin ↦ ?_⟩
  exact (hfin.preimage' fun a _ ↦ hfib a).subset (subset_preimage_image π _)

/-! ### Checks -/

/-- For `x ↦ 2x` on `ℤ`, `0` is periodic and `1` is not preperiodic. -/
example : IsPeriodicPt (fun x : ℤ ↦ 2 * x) 1 0 ∧ ¬ IsPreperiodicPt (fun x : ℤ ↦ 2 * x) 1 := by
  refine ⟨by simp [IsPeriodicPt, IsFixedPt], ?_⟩
  rintro ⟨r, s, hs, h⟩
  simp only [mul_left_iterate_apply_one] at h
  have hlt : (2 : ℤ) ^ r < 2 ^ (r + s) := pow_lt_pow_right₀ one_lt_two (by omega)
  exact hlt.ne' h

/-- For `x ↦ x²` on `ZMod 10`, every point is preperiodic, and `2` is not periodic: it is not a
square. -/
example : (∀ x : ZMod 10, IsPreperiodicPt (fun y ↦ y ^ 2) x) ∧
    2 ∉ periodicPts (fun y : ZMod 10 ↦ y ^ 2) := by
  refine ⟨fun x ↦ isPreperiodicPt_iff_finite_range_iterate.mpr (Set.toFinite _), fun h ↦ ?_⟩
  obtain ⟨y, hy⟩ := periodicPts_subset_range h
  revert hy
  revert y
  decide

end Function
