/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Order.Interval.Finset.Nat
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
  `Function.Semiconj.finite_forwardOrbit_iff_of_finite_fibres`: a semiconjugacy carries forward
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
  direction of `Semiconj.finite_forwardOrbit_iff_of_finite_fibres` its
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

/-- A point is preperiodic iff some iterate of it is a periodic point. -/
theorem isPreperiodicPt_iff_exists_mem_periodicPts :
    IsPreperiodicPt f x ↔ ∃ r, f^[r] x ∈ periodicPts f := by
  have hiter (r s : ℕ) : f^[r + s] x = f^[s] (f^[r] x) := by
    rw [add_comm, iterate_add_apply]
  constructor
  · rintro ⟨r, s, hs, hrs⟩
    exact ⟨r, mk_mem_periodicPts hs ((hiter r s).symm.trans hrs)⟩
  · rintro ⟨r, hr⟩
    obtain ⟨s, hs, hper⟩ := mem_periodicPts.mp hr
    exact ⟨r, s, hs, (hiter r s).trans hper⟩

/-- Some iterate of a preperiodic point is periodic. -/
theorem IsPreperiodicPt.exists_isPeriodicPt_iterate (hx : IsPreperiodicPt f x) :
    ∃ r n, 0 < n ∧ IsPeriodicPt f n (f^[r] x) := by
  obtain ⟨r, hr⟩ := isPreperiodicPt_iff_exists_mem_periodicPts.mp hx
  obtain ⟨n, hn, hper⟩ := mem_periodicPts.mp hr
  exact ⟨r, n, hn, hper⟩

/-- A periodic point of positive period is preperiodic. -/
theorem IsPeriodicPt.isPreperiodicPt {n : ℕ} (hn : 0 < n) (hx : IsPeriodicPt f n x) :
    IsPreperiodicPt f x :=
  isPreperiodicPt_iff_exists_mem_periodicPts.mpr ⟨0, mk_mem_periodicPts hn hx⟩

/-- Every point of `periodicPts f` is preperiodic. -/
theorem isPreperiodicPt_of_mem_periodicPts (hx : x ∈ periodicPts f) : IsPreperiodicPt f x :=
  isPreperiodicPt_iff_exists_mem_periodicPts.mpr ⟨0, hx⟩

/-- Iterates of a preperiodic point are preperiodic. -/
theorem IsPreperiodicPt.iterate (hx : IsPreperiodicPt f x) (m : ℕ) :
    IsPreperiodicPt f (f^[m] x) := by
  obtain ⟨r, n, hn, hper⟩ := hx.exists_isPeriodicPt_iterate
  have hcomm : f^[r] (f^[m] x) = f^[m] (f^[r] x) := by
    rw [← iterate_add_apply, add_comm, iterate_add_apply]
  refine isPreperiodicPt_iff_exists_mem_periodicPts.mpr ⟨r, ?_⟩
  rw [hcomm]
  exact mk_mem_periodicPts hn (hper.apply_iterate m)

/-- The image of a preperiodic point is preperiodic. -/
theorem IsPreperiodicPt.apply (hx : IsPreperiodicPt f x) : IsPreperiodicPt f (f x) :=
  hx.iterate 1

/-- **Preperiodic points have finite forward orbits**, and conversely. -/
theorem isPreperiodicPt_iff_finite_range_iterate :
    IsPreperiodicPt f x ↔ (Set.range fun n : ℕ ↦ f^[n] x).Finite := by
  constructor
  · rintro ⟨r, s, hs, hrs⟩
    have hper : IsPeriodicPt f s (f^[r] x) := by
      rw [IsPeriodicPt, IsFixedPt, ← iterate_add_apply, add_comm]
      exact hrs
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
    have : Finite (Set.range fun n : ℕ ↦ f^[n] x) := hfin.to_subtype
    obtain ⟨m, n, hmn, heq⟩ := Finite.exists_ne_map_eq_of_infinite
      (Set.rangeFactorization fun n : ℕ ↦ f^[n] x)
    have heq' : f^[m] x = f^[n] x := congrArg Subtype.val heq
    rcases lt_or_gt_of_ne hmn with h | h
    · exact ⟨m, n - m, by omega, by rw [Nat.add_sub_cancel' h.le]; exact heq'.symm⟩
    · exact ⟨n, m - n, by omega, by rw [Nat.add_sub_cancel' h.le]; exact heq'⟩

/-- A semiconjugacy carries preperiodic points to preperiodic points. -/
theorem IsPreperiodicPt.map {g : β → β} {π : β → α} (h : Semiconj π g f) {y : β}
    (hy : IsPreperiodicPt g y) : IsPreperiodicPt f (π y) := by
  obtain ⟨r, s, hs, hrs⟩ := hy
  refine ⟨r, s, hs, ?_⟩
  rw [← (h.iterate_right (r + s)).eq, ← (h.iterate_right r).eq, hrs]

/-! ### Forward orbits of sets -/

/-- The **forward orbit** `⋃ n, f^[n] '' s` of a set `s` under `f`. -/
def forwardOrbit (f : α → α) (s : Set α) : Set α :=
  ⋃ n : ℕ, f^[n] '' s

variable {s t : Set α}

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

theorem forwardOrbit_mono (hst : s ⊆ t) : forwardOrbit f s ⊆ forwardOrbit f t :=
  forwardOrbit_subset_of_mapsTo (hst.trans subset_forwardOrbit) mapsTo_forwardOrbit

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

/-- **The forward orbit of a finite set is finite iff each of its points is preperiodic.** -/
theorem finite_forwardOrbit_iff (hs : s.Finite) :
    (forwardOrbit f s).Finite ↔ ∀ x ∈ s, IsPreperiodicPt f x := by
  simp_rw [isPreperiodicPt_iff_finite_range_iterate]
  constructor
  · intro h x hx
    exact h.subset (by rw [← forwardOrbit_singleton]; exact forwardOrbit_mono (by simpa))
  · intro h
    rw [forwardOrbit_eq_biUnion_range_iterate]
    exact hs.biUnion h

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
theorem Semiconj.finite_forwardOrbit_iff_of_finite_fibres {g : β → β} {π : β → α}
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
