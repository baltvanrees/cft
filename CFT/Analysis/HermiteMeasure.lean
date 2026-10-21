/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Balt van Rees
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Fejér–Hermite Measure Estimate on `ℤ`

This file proves the quantitative Fejér–Hermite measure estimate on the integer lattice `ℤ`.
Given two finite positive measures `μ, ν` on `ℝ` such that `ν` is supported on `ℤ` and their
Fourier transforms differ by at most `ε` on `[-2π, 2π]`, we bound
`|∫ ψ dμ - ∫ ψ dν|` for any compactly supported `C^2` test function `ψ`
by `C_N * ε * M_ψ`.
-/

open MeasureTheory Set Filter TopologicalSpace intervalIntegral
open scoped Real Topology

namespace CFT.LightconeBootstrap

/-! ## 1. Lattice Distance and Trigonometric Lower Bound -/

/-- Distance from `u : ℝ` to the nearest integer `round u`. -/
noncomputable def distInt (u : ℝ) : ℝ := |u - round u|

lemma distInt_nonneg (u : ℝ) : 0 ≤ distInt u := abs_nonneg _

lemma distInt_le_half (u : ℝ) : distInt u ≤ 1 / 2 := abs_sub_round u

@[simp]
lemma distInt_intCast (n : ℤ) : distInt (n : ℝ) = 0 := by
  simp [distInt, round_intCast]

@[fun_prop]
lemma measurable_distInt : Measurable distInt := by
  have h : distInt = fun u : ℝ => |u - (⌊u + 1 / 2⌋ : ℝ)| := by
    ext u
    simp [distInt, round_eq]
  rw [h]
  have hfloor : Measurable (fun x : ℝ => (⌊x⌋ : ℝ)) :=
    ((Int.cast_mono (R := ℝ)).comp Int.floor_mono).measurable
  have hsub : Measurable (fun u : ℝ => u - (⌊u + 1 / 2⌋ : ℝ)) :=
    measurable_id.sub (hfloor.comp (measurable_id.add_const (1 / 2)))
  exact continuous_abs.measurable.comp hsub

lemma two_mul_le_sin_pi_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    2 * x ≤ Real.sin (π * x) := by
  have h1 : 0 ≤ π * x := mul_nonneg Real.pi_nonneg hx0
  have h2 : π * x ≤ π / 2 := by
    calc π * x ≤ π * (1 / 2) := mul_le_mul_of_nonneg_left hx1 Real.pi_nonneg
    _ = π / 2 := by ring
  have h3 := Real.mul_le_sin h1 h2
  have hpi : π ≠ 0 := Real.pi_ne_zero
  calc 2 * x = 2 / π * (π * x) := by field_simp
  _ ≤ Real.sin (π * x) := h3

lemma four_mul_sq_le_sin_pi_mul_sq {x : ℝ} (hx : |x| ≤ 1 / 2) :
    4 * x ^ 2 ≤ (Real.sin (π * x)) ^ 2 := by
  have h := two_mul_le_sin_pi_mul (abs_nonneg x) hx
  have habs : |Real.sin (π * |x|)| = |Real.sin (π * x)| := by
    rcases le_total 0 x with h0 | h0
    · rw [abs_of_nonneg h0]
    · rw [abs_of_nonpos h0, mul_neg, Real.sin_neg, abs_neg]
  have h2 : 2 * |x| ≤ |Real.sin (π * x)| := by
    rw [← habs]
    exact h.trans (le_abs_self _)
  have h3 : (2 * |x|) ^ 2 ≤ |Real.sin (π * x)| ^ 2 :=
    sq_le_sq.mpr (by rw [abs_abs, abs_of_nonneg (by positivity)]; exact h2)
  calc 4 * x ^ 2 = (2 * |x|) ^ 2 := by ring_nf; rw [sq_abs]
  _ ≤ |Real.sin (π * x)| ^ 2 := h3
  _ = (Real.sin (π * x)) ^ 2 := sq_abs _

lemma one_sub_cos_two_pi_mul_eq (u : ℝ) :
    1 - Real.cos (2 * π * u) = 2 * (Real.sin (π * (u - round u))) ^ 2 := by
  have h1 : 2 * π * u = 2 * (π * (u - round u)) + (round u : ℤ) * (2 * π) := by ring
  rw [h1, Real.cos_add_int_mul_two_pi, Real.cos_two_mul', Real.cos_sq']
  ring

lemma eight_mul_distInt_sq_le (u : ℝ) :
    8 * (distInt u) ^ 2 ≤ 1 - Real.cos (2 * π * u) := by
  rw [one_sub_cos_two_pi_mul_eq]
  have h := four_mul_sq_le_sin_pi_mul_sq (distInt_le_half u)
  unfold distInt at *
  linarith [sq_abs (u - round u)]

lemma integral_eq_zero_of_forall_int_eq_zero {ν : Measure ℝ}
    (hν : ν (univ \ range (Int.cast : ℤ → ℝ)) = 0) {f : ℝ → ℝ}
    (hf : ∀ n : ℤ, f n = 0) : ∫ u, f u ∂ν = 0 := by
  have hae : f =ᵐ[ν] 0 := by
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun u hu => ?_) hν
    simp only [Set.mem_sdiff, mem_univ, mem_range, true_and, not_exists]
    rintro n rfl
    exact hu (hf n)
  exact integral_eq_zero_of_ae hae

/-! ## 2. Parametric Differentiation on `[0, 2π]` and Fejér Kernels -/

lemma hasDerivAt_integral_mul_cos {g : ℝ → ℝ} (hg : Continuous g) (u : ℝ) :
    HasDerivAt (fun x => ∫ t in (0 : ℝ)..(2 * π), g t * Real.cos (t * x))
      (∫ t in (0 : ℝ)..(2 * π), -(g t * t) * Real.sin (t * u)) u := by
  let F : ℝ → ℝ → ℝ := fun x t => g t * Real.cos (t * x)
  let F' : ℝ → ℝ → ℝ := fun x t => -(g t * t) * Real.sin (t * x)
  have hF_cont : ∀ x : ℝ, Continuous (F x) :=
    fun x => hg.mul (Real.continuous_cos.comp (continuous_id.mul continuous_const))
  have hF'_cont : ∀ x : ℝ, Continuous (F' x) :=
    fun x => (hg.mul continuous_id).neg.mul
      (Real.continuous_sin.comp (continuous_id.mul continuous_const))
  have h_bound_cont : Continuous (fun t => |g t * t|) := (hg.mul continuous_id).abs
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F')
    (s := univ) (bound := fun t => |g t * t|) univ_mem
    (Eventually.of_forall fun x => (hF_cont x).aestronglyMeasurable)
    ((hF_cont u).intervalIntegrable 0 (2 * π))
    (hF'_cont u).aestronglyMeasurable ?_
    (h_bound_cont.intervalIntegrable 0 (2 * π)) ?_).2
  · refine ae_of_all _ (fun t _ x _ => ?_)
    change ‖-(g t * t) * Real.sin (t * x)‖ ≤ |g t * t|
    rw [Real.norm_eq_abs, abs_mul, abs_neg]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  · refine ae_of_all _ (fun t _ x _ => ?_)
    have h1 : HasDerivAt (fun x => t * x) t x := by
      simpa using (hasDerivAt_id x).const_mul t
    have h2 : HasDerivAt (F · t) (g t * (-Real.sin (t * x) * t)) x :=
      (h1.cos).const_mul (g t)
    convert h2 using 1
    change -(g t * t) * Real.sin (t * x) = g t * (-Real.sin (t * x) * t)
    ring

lemma hasDerivAt_integral_mul_sin {g : ℝ → ℝ} (hg : Continuous g) (u : ℝ) :
    HasDerivAt (fun x => ∫ t in (0 : ℝ)..(2 * π), g t * Real.sin (t * x))
      (∫ t in (0 : ℝ)..(2 * π), (g t * t) * Real.cos (t * u)) u := by
  let F : ℝ → ℝ → ℝ := fun x t => g t * Real.sin (t * x)
  let F' : ℝ → ℝ → ℝ := fun x t => (g t * t) * Real.cos (t * x)
  have hF_cont : ∀ x : ℝ, Continuous (F x) :=
    fun x => hg.mul (Real.continuous_sin.comp (continuous_id.mul continuous_const))
  have hF'_cont : ∀ x : ℝ, Continuous (F' x) :=
    fun x => (hg.mul continuous_id).mul
      (Real.continuous_cos.comp (continuous_id.mul continuous_const))
  have h_bound_cont : Continuous (fun t => |g t * t|) := (hg.mul continuous_id).abs
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F')
    (s := univ) (bound := fun t => |g t * t|) univ_mem
    (Eventually.of_forall fun x => (hF_cont x).aestronglyMeasurable)
    ((hF_cont u).intervalIntegrable 0 (2 * π))
    (hF'_cont u).aestronglyMeasurable ?_
    (h_bound_cont.intervalIntegrable 0 (2 * π)) ?_).2
  · refine ae_of_all _ (fun t _ x _ => ?_)
    change ‖(g t * t) * Real.cos (t * x)‖ ≤ |g t * t|
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  · refine ae_of_all _ (fun t _ x _ => ?_)
    have h1 : HasDerivAt (fun x => t * x) t x := by
      simpa using (hasDerivAt_id x).const_mul t
    have h2 : HasDerivAt (F · t) (g t * (Real.cos (t * x) * t)) x :=
      (h1.sin).const_mul (g t)
    convert h2 using 1
    change (g t * t) * Real.cos (t * x) = g t * (Real.cos (t * x) * t)
    ring

/-- The Fejér kernel `K(u) = (sin(π u) / (π u))^2`, defined smoothly on `ℝ` via its Fourier
representation on `[0, 2π]`. -/
noncomputable def fejerKernel (u : ℝ) : ℝ :=
  (2 * π ^ 2)⁻¹ * ∫ t in (0 : ℝ)..(2 * π), (2 * π - t) * Real.cos (t * u)

/-- First derivative of `fejerKernel`. -/
noncomputable def fejerKernelDeriv (u : ℝ) : ℝ :=
  (2 * π ^ 2)⁻¹ * ∫ t in (0 : ℝ)..(2 * π), -((2 * π - t) * t) * Real.sin (t * u)

/-- Second derivative of `fejerKernel`. -/
noncomputable def fejerKernelDeriv2 (u : ℝ) : ℝ :=
  (2 * π ^ 2)⁻¹ * ∫ t in (0 : ℝ)..(2 * π), (-((2 * π - t) * t) * t) * Real.cos (t * u)

/-- The Fejér slope kernel `u K(u) = (sin(π u))^2 / (π^2 u)`, defined smoothly on `ℝ` via its
Fourier representation on `[0, 2π]`. -/
noncomputable def fejerSlopeKernel (u : ℝ) : ℝ :=
  (2 * π ^ 2)⁻¹ * ∫ t in (0 : ℝ)..(2 * π), 1 * Real.sin (t * u)

/-- First derivative of `fejerSlopeKernel`. -/
noncomputable def fejerSlopeKernelDeriv (u : ℝ) : ℝ :=
  (2 * π ^ 2)⁻¹ * ∫ t in (0 : ℝ)..(2 * π), (1 * t) * Real.cos (t * u)

/-- Second derivative of `fejerSlopeKernel`. -/
noncomputable def fejerSlopeKernelDeriv2 (u : ℝ) : ℝ :=
  (2 * π ^ 2)⁻¹ * ∫ t in (0 : ℝ)..(2 * π), -((1 * t) * t) * Real.sin (t * u)

lemma hasDerivAt_fejerKernel (u : ℝ) :
    HasDerivAt fejerKernel (fejerKernelDeriv u) u :=
  (hasDerivAt_integral_mul_cos (continuous_const.sub continuous_id) u).const_mul (2 * π ^ 2)⁻¹

lemma hasDerivAt_fejerKernelDeriv (u : ℝ) :
    HasDerivAt fejerKernelDeriv (fejerKernelDeriv2 u) u :=
  (hasDerivAt_integral_mul_sin
    ((continuous_const.sub continuous_id).mul continuous_id).neg u).const_mul (2 * π ^ 2)⁻¹

lemma hasDerivAt_fejerSlopeKernel (u : ℝ) :
    HasDerivAt fejerSlopeKernel (fejerSlopeKernelDeriv u) u :=
  (hasDerivAt_integral_mul_sin continuous_const u).const_mul (2 * π ^ 2)⁻¹

lemma hasDerivAt_fejerSlopeKernelDeriv (u : ℝ) :
    HasDerivAt fejerSlopeKernelDeriv (fejerSlopeKernelDeriv2 u) u :=
  (hasDerivAt_integral_mul_cos (continuous_const.mul continuous_id) u).const_mul (2 * π ^ 2)⁻¹

@[simp]
lemma deriv_fejerKernel : deriv fejerKernel = fejerKernelDeriv := by
  ext u; exact (hasDerivAt_fejerKernel u).deriv

@[simp]
lemma deriv_fejerKernelDeriv : deriv fejerKernelDeriv = fejerKernelDeriv2 := by
  ext u; exact (hasDerivAt_fejerKernelDeriv u).deriv

@[simp]
lemma deriv_fejerSlopeKernel : deriv fejerSlopeKernel = fejerSlopeKernelDeriv := by
  ext u; exact (hasDerivAt_fejerSlopeKernel u).deriv

@[simp]
lemma deriv_fejerSlopeKernelDeriv : deriv fejerSlopeKernelDeriv = fejerSlopeKernelDeriv2 := by
  ext u; exact (hasDerivAt_fejerSlopeKernelDeriv u).deriv

lemma continuous_fejerKernel : Continuous fejerKernel :=
  Differentiable.continuous (fun u => (hasDerivAt_fejerKernel u).differentiableAt)

lemma continuous_fejerKernelDeriv : Continuous fejerKernelDeriv :=
  Differentiable.continuous (fun u => (hasDerivAt_fejerKernelDeriv u).differentiableAt)

lemma continuous_fejerSlopeKernel : Continuous fejerSlopeKernel :=
  Differentiable.continuous (fun u => (hasDerivAt_fejerSlopeKernel u).differentiableAt)

lemma continuous_fejerSlopeKernelDeriv : Continuous fejerSlopeKernelDeriv :=
  Differentiable.continuous (fun u => (hasDerivAt_fejerSlopeKernelDeriv u).differentiableAt)

/-! ## 3. Closed Forms, Integer Interpolation Values, and Global Bounds -/

lemma integral_two_pi_sub :
    ∫ t in (0 : ℝ)..(2 * π), (2 * π - t) = 2 * π ^ 2 := by
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) (2 * π),
      HasDerivAt (fun x : ℝ => 2 * π * x - x ^ 2 / 2) (2 * π - t) t := by
    intro t _
    have h1 : HasDerivAt (fun x : ℝ => 2 * π * x) (2 * π * 1) t :=
      (hasDerivAt_id t).const_mul (2 * π)
    have h2 : HasDerivAt (fun x : ℝ => x ^ 2 / 2) ((2 : ℝ) * t ^ (2 - 1) / 2) t :=
      (hasDerivAt_pow 2 t).div_const 2
    convert h1.sub h2 using 1
    ring
  rw [integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_const.sub continuous_id).intervalIntegrable _ _)]
  ring

lemma integral_one_two_pi :
    ∫ _t in (0 : ℝ)..(2 * π), (1 : ℝ) = 2 * π := by
  simp [intervalIntegral.integral_const]

lemma integral_id_two_pi :
    ∫ t in (0 : ℝ)..(2 * π), t = 2 * π ^ 2 := by
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) (2 * π),
      HasDerivAt (fun x : ℝ => x ^ 2 / 2) t t := by
    intro t _
    convert (hasDerivAt_pow 2 t).div_const 2 using 1
    ring
  rw [integral_eq_sub_of_hasDerivAt hderiv (continuous_id.intervalIntegrable _ _)]
  ring

lemma integral_sq_two_pi :
    ∫ t in (0 : ℝ)..(2 * π), t ^ 2 = 8 * π ^ 3 / 3 := by
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) (2 * π),
      HasDerivAt (fun x : ℝ => x ^ 3 / 3) (t ^ 2) t := by
    intro t _
    convert (hasDerivAt_pow 3 t).div_const 3 using 1
    ring
  rw [integral_eq_sub_of_hasDerivAt hderiv ((continuous_pow 2).intervalIntegrable _ _)]
  ring

lemma integral_two_pi_sub_mul_sq :
    ∫ t in (0 : ℝ)..(2 * π), (2 * π - t) * t ^ 2 = 4 * π ^ 4 / 3 := by
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) (2 * π),
      HasDerivAt (fun x : ℝ => 2 * π * (x ^ 3 / 3) - x ^ 4 / 4) ((2 * π - t) * t ^ 2) t := by
    intro t _
    have h1 := ((hasDerivAt_pow 3 t).div_const 3).const_mul (2 * π)
    have h2 := (hasDerivAt_pow 4 t).div_const 4
    convert h1.sub h2 using 1
    ring
  have hcont : Continuous (fun t : ℝ => (2 * π - t) * t ^ 2) :=
    (continuous_const.sub continuous_id).mul (continuous_pow 2)
  rw [integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  ring

@[simp]
lemma fejerKernel_zero : fejerKernel 0 = 1 := by
  unfold fejerKernel
  simp only [mul_zero, Real.cos_zero, mul_one, integral_two_pi_sub]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp

@[simp]
lemma fejerKernelDeriv_zero : fejerKernelDeriv 0 = 0 := by
  unfold fejerKernelDeriv
  simp

@[simp]
lemma fejerSlopeKernel_zero : fejerSlopeKernel 0 = 0 := by
  unfold fejerSlopeKernel
  simp

@[simp]
lemma fejerSlopeKernelDeriv_zero : fejerSlopeKernelDeriv 0 = 1 := by
  unfold fejerSlopeKernelDeriv
  simp only [mul_zero, Real.cos_zero, mul_one, one_mul, integral_id_two_pi]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp

lemma fejerSlopeKernel_eq_of_ne_zero {u : ℝ} (hu : u ≠ 0) :
    fejerSlopeKernel u = (1 - Real.cos (2 * π * u)) / (2 * π ^ 2 * u) := by
  unfold fejerSlopeKernel
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) (2 * π),
      HasDerivAt (fun x : ℝ => -Real.cos (x * u) / u) (1 * Real.sin (t * u)) t := by
    intro t _
    have h1 : HasDerivAt (fun x : ℝ => x * u) (1 * u) t := (hasDerivAt_id t).mul_const u
    have h2 := h1.cos.neg.div_const u
    convert h2 using 1
    field_simp
  have hcont : Continuous (fun t : ℝ => 1 * Real.sin (t * u)) :=
    continuous_const.mul (Real.continuous_sin.comp (continuous_id.mul continuous_const))
  rw [integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  simp only [zero_mul, Real.cos_zero]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

lemma fejerKernel_eq_of_ne_zero {u : ℝ} (hu : u ≠ 0) :
    fejerKernel u = (1 - Real.cos (2 * π * u)) / (2 * π ^ 2 * u ^ 2) := by
  unfold fejerKernel
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) (2 * π),
      HasDerivAt (fun x : ℝ => (2 * π - x) * (Real.sin (x * u) / u) - Real.cos (x * u) / u ^ 2)
        ((2 * π - t) * Real.cos (t * u)) t := by
    intro t _
    have h1 : HasDerivAt (fun x : ℝ => x * u) (1 * u) t := (hasDerivAt_id t).mul_const u
    have hsin : HasDerivAt (fun x : ℝ => Real.sin (x * u) / u) (Real.cos (t * u)) t := by
      convert h1.sin.div_const u using 1
      field_simp
    have hsub : HasDerivAt (fun x : ℝ => 2 * π - x) (-1) t :=
      (hasDerivAt_id t).const_sub (2 * π)
    have hcos : HasDerivAt (fun x : ℝ => Real.cos (x * u) / u ^ 2)
        (-Real.sin (t * u) / u) t := by
      convert h1.cos.div_const (u ^ 2) using 1
      field_simp
    convert (hsub.mul hsin).sub hcos using 1
    ring
  have hcont : Continuous (fun t : ℝ => (2 * π - t) * Real.cos (t * u)) :=
    (continuous_const.sub continuous_id).mul
      (Real.continuous_cos.comp (continuous_id.mul continuous_const))
  rw [integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  simp only [sub_self, zero_mul, Real.sin_zero, zero_div, mul_zero, Real.cos_zero, zero_sub]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

lemma fejerSlopeKernel_eq_mul_fejerKernel (u : ℝ) :
    fejerSlopeKernel u = u * fejerKernel u := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  · rw [fejerSlopeKernel_eq_of_ne_zero hu, fejerKernel_eq_of_ne_zero hu]
    have hpi : π ≠ 0 := Real.pi_ne_zero
    field_simp

lemma fejerSlopeKernelDeriv_eq_add (u : ℝ) :
    fejerSlopeKernelDeriv u = fejerKernel u + u * fejerKernelDeriv u := by
  have h1 := hasDerivAt_fejerSlopeKernel u
  have h2 : HasDerivAt (fun x => x * fejerKernel x)
      (1 * fejerKernel u + u * fejerKernelDeriv u) u :=
    (hasDerivAt_id u).mul (hasDerivAt_fejerKernel u)
  have heq : fejerSlopeKernel = fun x => x * fejerKernel x :=
    funext fejerSlopeKernel_eq_mul_fejerKernel
  rw [heq] at h1
  linarith [h1.unique h2]

lemma fejerSlopeKernelDeriv_eq_of_ne_zero {u : ℝ} (hu : u ≠ 0) :
    fejerSlopeKernelDeriv u =
      (2 * π * u * Real.sin (2 * π * u) + Real.cos (2 * π * u) - 1) / (2 * π ^ 2 * u ^ 2) := by
  unfold fejerSlopeKernelDeriv
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) (2 * π),
      HasDerivAt (fun x : ℝ => x * (Real.sin (x * u) / u) + Real.cos (x * u) / u ^ 2)
        ((1 * t) * Real.cos (t * u)) t := by
    intro t _
    have h1 : HasDerivAt (fun x : ℝ => x * u) (1 * u) t := (hasDerivAt_id t).mul_const u
    have hsin : HasDerivAt (fun x : ℝ => Real.sin (x * u) / u) (Real.cos (t * u)) t := by
      convert h1.sin.div_const u using 1
      field_simp
    have hcos : HasDerivAt (fun x : ℝ => Real.cos (x * u) / u ^ 2)
        (-Real.sin (t * u) / u) t := by
      convert h1.cos.div_const (u ^ 2) using 1
      field_simp
    have hid : HasDerivAt (fun x : ℝ => x) 1 t := hasDerivAt_id t
    have hsum : HasDerivAt (fun x : ℝ => x * (Real.sin (x * u) / u) + Real.cos (x * u) / u ^ 2)
        (1 * (Real.sin (t * u) / u) + t * Real.cos (t * u) + -Real.sin (t * u) / u) t :=
      (hid.mul hsin).add hcos
    convert hsum using 1
    ring
  have hcont : Continuous (fun t : ℝ => (1 * t) * Real.cos (t * u)) :=
    (continuous_const.mul continuous_id).mul
      (Real.continuous_cos.comp (continuous_id.mul continuous_const))
  rw [integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  simp only [zero_mul, Real.sin_zero, zero_div, Real.cos_zero, zero_add]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp

lemma cos_two_pi_mul_intCast (m : ℤ) : Real.cos (2 * π * (m : ℝ)) = 1 := by
  have h : 2 * π * (m : ℝ) = (m : ℝ) * (2 * π) := by ring
  rw [h, Real.cos_int_mul_two_pi]

lemma sin_two_pi_mul_intCast (m : ℤ) : Real.sin (2 * π * (m : ℝ)) = 0 := by
  have h : 2 * π * (m : ℝ) = ((2 * m : ℤ) : ℝ) * π := by push_cast; ring
  rw [h, Real.sin_int_mul_pi]

lemma fejerKernel_intCast_of_ne_zero {m : ℤ} (hm : m ≠ 0) :
    fejerKernel (m : ℝ) = 0 := by
  have hm' : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
  rw [fejerKernel_eq_of_ne_zero hm', cos_two_pi_mul_intCast, sub_self, zero_div]

@[simp]
lemma fejerSlopeKernel_intCast (m : ℤ) :
    fejerSlopeKernel (m : ℝ) = 0 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · rw [fejerSlopeKernel_eq_mul_fejerKernel, fejerKernel_intCast_of_ne_zero hm, mul_zero]

lemma fejerSlopeKernelDeriv_intCast_of_ne_zero {m : ℤ} (hm : m ≠ 0) :
    fejerSlopeKernelDeriv (m : ℝ) = 0 := by
  have hm' : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
  rw [fejerSlopeKernelDeriv_eq_of_ne_zero hm', sin_two_pi_mul_intCast, cos_two_pi_mul_intCast]
  ring

@[simp]
lemma fejerKernelDeriv_intCast (m : ℤ) :
    fejerKernelDeriv (m : ℝ) = 0 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · have h := fejerSlopeKernelDeriv_eq_add (m : ℝ)
    rw [fejerSlopeKernelDeriv_intCast_of_ne_zero hm, fejerKernel_intCast_of_ne_zero hm,
      zero_add] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (Int.cast_ne_zero.mpr hm)

lemma abs_intervalIntegral_le_of_nonneg {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hle : ∀ t ∈ Icc a b, |f t| ≤ g t) :
    |∫ t in a..b, f t| ≤ ∫ t in a..b, g t := by
  rw [← Real.norm_eq_abs]
  exact (intervalIntegral.norm_integral_le_integral_norm hab).trans
    (intervalIntegral.integral_mono_on hab (hf.norm.intervalIntegrable _ _)
      (hg.intervalIntegrable _ _) (fun t ht => by simpa [Real.norm_eq_abs] using hle t ht))

lemma abs_fejerKernel_le_one (u : ℝ) : |fejerKernel u| ≤ 1 := by
  unfold fejerKernel
  rw [abs_mul, abs_of_pos (by positivity)]
  have hle : |∫ t in (0 : ℝ)..(2 * π), (2 * π - t) * Real.cos (t * u)| ≤
      ∫ t in (0 : ℝ)..(2 * π), (2 * π - t) := by
    refine abs_intervalIntegral_le_of_nonneg (by positivity)
      ((continuous_const.sub continuous_id).mul
        (Real.continuous_cos.comp (continuous_id.mul continuous_const)))
      (continuous_const.sub continuous_id) (fun t ht => ?_)
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr ht.2)]
    exact mul_le_of_le_one_right (sub_nonneg.mpr ht.2) (Real.abs_cos_le_one _)
  rw [integral_two_pi_sub] at hle
  have hpi : 0 < 2 * π ^ 2 := by positivity
  calc (2 * π ^ 2)⁻¹ * |∫ t in (0 : ℝ)..(2 * π), (2 * π - t) * Real.cos (t * u)|
    ≤ (2 * π ^ 2)⁻¹ * (2 * π ^ 2) := mul_le_mul_of_nonneg_left hle (by positivity)
  _ = 1 := inv_mul_cancel₀ hpi.ne'

lemma abs_fejerSlopeKernel_le (u : ℝ) : |fejerSlopeKernel u| ≤ 1 / π := by
  unfold fejerSlopeKernel
  rw [abs_mul, abs_of_pos (by positivity)]
  have hle : |∫ t in (0 : ℝ)..(2 * π), 1 * Real.sin (t * u)| ≤
      ∫ _t in (0 : ℝ)..(2 * π), (1 : ℝ) := by
    refine abs_intervalIntegral_le_of_nonneg (by positivity)
      (continuous_const.mul (Real.continuous_sin.comp (continuous_id.mul continuous_const)))
      continuous_const (fun t _ => ?_)
    simpa using Real.abs_sin_le_one (t * u)
  rw [integral_one_two_pi] at hle
  have hpi : π ≠ 0 := Real.pi_ne_zero
  calc (2 * π ^ 2)⁻¹ * |∫ t in (0 : ℝ)..(2 * π), 1 * Real.sin (t * u)|
    ≤ (2 * π ^ 2)⁻¹ * (2 * π) := mul_le_mul_of_nonneg_left hle (by positivity)
  _ = 1 / π := by field_simp

lemma abs_fejerKernelDeriv2_le (u : ℝ) : |fejerKernelDeriv2 u| ≤ 2 * π ^ 2 / 3 := by
  unfold fejerKernelDeriv2
  rw [abs_mul, abs_of_pos (by positivity)]
  have hle : |∫ t in (0 : ℝ)..(2 * π), (-((2 * π - t) * t) * t) * Real.cos (t * u)| ≤
      ∫ t in (0 : ℝ)..(2 * π), (2 * π - t) * t ^ 2 := by
    refine abs_intervalIntegral_le_of_nonneg (by positivity)
      ((((continuous_const.sub continuous_id).mul continuous_id).neg.mul continuous_id).mul
        (Real.continuous_cos.comp (continuous_id.mul continuous_const)))
      ((continuous_const.sub continuous_id).mul (continuous_pow 2)) (fun t ht => ?_)
    have hnonneg : 0 ≤ (2 * π - t) * t ^ 2 :=
      mul_nonneg (sub_nonneg.mpr ht.2) (sq_nonneg t)
    have hrew : (-((2 * π - t) * t) * t) * Real.cos (t * u) =
        -((2 * π - t) * t ^ 2) * Real.cos (t * u) := by ring
    rw [hrew, abs_mul, abs_neg, abs_of_nonneg hnonneg]
    exact mul_le_of_le_one_right hnonneg (Real.abs_cos_le_one _)
  rw [integral_two_pi_sub_mul_sq] at hle
  have hpi : π ≠ 0 := Real.pi_ne_zero
  calc (2 * π ^ 2)⁻¹ *
      |∫ t in (0 : ℝ)..(2 * π), (-((2 * π - t) * t) * t) * Real.cos (t * u)|
    ≤ (2 * π ^ 2)⁻¹ * (4 * π ^ 4 / 3) := mul_le_mul_of_nonneg_left hle (by positivity)
  _ = 2 * π ^ 2 / 3 := by field_simp; ring

lemma abs_fejerSlopeKernelDeriv2_le (u : ℝ) : |fejerSlopeKernelDeriv2 u| ≤ 4 * π / 3 := by
  unfold fejerSlopeKernelDeriv2
  rw [abs_mul, abs_of_pos (by positivity)]
  have hle : |∫ t in (0 : ℝ)..(2 * π), -((1 * t) * t) * Real.sin (t * u)| ≤
      ∫ t in (0 : ℝ)..(2 * π), t ^ 2 := by
    refine abs_intervalIntegral_le_of_nonneg (by positivity)
      (((continuous_const.mul continuous_id).mul continuous_id).neg.mul
        (Real.continuous_sin.comp (continuous_id.mul continuous_const)))
      (continuous_pow 2) (fun t _ => ?_)
    have hrew : -((1 * t) * t) * Real.sin (t * u) = -(t ^ 2) * Real.sin (t * u) := by ring
    rw [hrew, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg t)]
    exact mul_le_of_le_one_right (sq_nonneg t) (Real.abs_sin_le_one _)
  rw [integral_sq_two_pi] at hle
  have hpi : π ≠ 0 := Real.pi_ne_zero
  calc (2 * π ^ 2)⁻¹ * |∫ t in (0 : ℝ)..(2 * π), -((1 * t) * t) * Real.sin (t * u)|
    ≤ (2 * π ^ 2)⁻¹ * (8 * π ^ 3 / 3) := mul_le_mul_of_nonneg_left hle (by positivity)
  _ = 4 * π / 3 := by field_simp; ring

/-! ## 4. Fourier Difference Bounds and Bandlimited Pairing via Fubini -/

lemma integrable_of_continuous_bounded {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ} (hb : ∀ u, |f u| ≤ M) :
    Integrable f ρ :=
  Integrable.of_bound hf.aestronglyMeasurable M
    (ae_of_all _ fun u => by simpa [Real.norm_eq_abs] using hb u)

lemma norm_integral_exp_sub_shift_le {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {t ε : ℝ} (a : ℝ)
    (ht : ‖(∫ u : ℝ, Complex.exp (Complex.I * (t : ℂ) * (u : ℂ)) ∂μ) -
      (∫ u : ℝ, Complex.exp (Complex.I * (t : ℂ) * (u : ℂ)) ∂ν)‖ ≤ ε) :
    ‖(∫ u : ℝ, Complex.exp (((t * (u - a) : ℝ) : ℂ) * Complex.I) ∂μ) -
      (∫ u : ℝ, Complex.exp (((t * (u - a) : ℝ) : ℂ) * Complex.I) ∂ν)‖ ≤ ε := by
  have hrew : ∀ u : ℝ, Complex.exp (((t * (u - a) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((-t * a : ℝ) : ℂ) * Complex.I) *
        Complex.exp (Complex.I * (t : ℂ) * (u : ℂ)) := by
    intro u
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hrew, MeasureTheory.integral_const_mul, ← mul_sub, norm_mul,
    Complex.norm_exp_ofReal_mul_I, one_mul]
  exact ht

lemma abs_integral_cos_sub_le {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {t ε : ℝ} (a : ℝ)
    (ht : ‖(∫ u : ℝ, Complex.exp (Complex.I * (t : ℂ) * (u : ℂ)) ∂μ) -
      (∫ u : ℝ, Complex.exp (Complex.I * (t : ℂ) * (u : ℂ)) ∂ν)‖ ≤ ε) :
    |(∫ u : ℝ, Real.cos (t * (u - a)) ∂μ) -
      (∫ u : ℝ, Real.cos (t * (u - a)) ∂ν)| ≤ ε := by
  have hE_int : ∀ ρ : Measure ℝ, [IsFiniteMeasure ρ] →
      Integrable (fun u : ℝ => Complex.exp (((t * (u - a) : ℝ) : ℂ) * Complex.I)) ρ := by
    intro ρ _
    have hcont : Continuous
        (fun u : ℝ => Complex.exp (((t * (u - a) : ℝ) : ℂ) * Complex.I)) :=
      Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp
          (continuous_const.mul (continuous_id.sub continuous_const))).mul continuous_const)
    exact Integrable.of_bound hcont.aestronglyMeasurable 1
      (ae_of_all _ fun u => by rw [Complex.norm_exp_ofReal_mul_I])
  have hre_μ : (∫ u : ℝ, Complex.exp (((t * (u - a) : ℝ) : ℂ) * Complex.I) ∂μ).re =
      ∫ u : ℝ, Real.cos (t * (u - a)) ∂μ := by
    have h := (Complex.reCLM.integral_comp_comm (hE_int μ)).symm
    simp only [Complex.reCLM_apply, Complex.exp_ofReal_mul_I_re] at h
    exact h
  have hre_ν : (∫ u : ℝ, Complex.exp (((t * (u - a) : ℝ) : ℂ) * Complex.I) ∂ν).re =
      ∫ u : ℝ, Real.cos (t * (u - a)) ∂ν := by
    have h := (Complex.reCLM.integral_comp_comm (hE_int ν)).symm
    simp only [Complex.reCLM_apply, Complex.exp_ofReal_mul_I_re] at h
    exact h
  have hre : ((∫ u : ℝ, Complex.exp (((t * (u - a) : ℝ) : ℂ) * Complex.I) ∂μ) -
      (∫ u : ℝ, Complex.exp (((t * (u - a) : ℝ) : ℂ) * Complex.I) ∂ν)).re =
      (∫ u : ℝ, Real.cos (t * (u - a)) ∂μ) -
        (∫ u : ℝ, Real.cos (t * (u - a)) ∂ν) := by
    rw [Complex.sub_re, hre_μ, hre_ν]
  rw [← hre]
  exact (Complex.abs_re_le_norm _).trans (norm_integral_exp_sub_shift_le a ht)

lemma abs_integral_sin_sub_le {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {t ε : ℝ} (a : ℝ)
    (ht : ‖(∫ u : ℝ, Complex.exp (Complex.I * (t : ℂ) * (u : ℂ)) ∂μ) -
      (∫ u : ℝ, Complex.exp (Complex.I * (t : ℂ) * (u : ℂ)) ∂ν)‖ ≤ ε) :
    |(∫ u : ℝ, Real.sin (t * (u - a)) ∂μ) -
      (∫ u : ℝ, Real.sin (t * (u - a)) ∂ν)| ≤ ε := by
  have hE_int : ∀ ρ : Measure ℝ, [IsFiniteMeasure ρ] →
      Integrable (fun u : ℝ => Complex.exp (((t * (u - a) : ℝ) : ℂ) * Complex.I)) ρ := by
    intro ρ _
    have hcont : Continuous
        (fun u : ℝ => Complex.exp (((t * (u - a) : ℝ) : ℂ) * Complex.I)) :=
      Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp
          (continuous_const.mul (continuous_id.sub continuous_const))).mul continuous_const)
    exact Integrable.of_bound hcont.aestronglyMeasurable 1
      (ae_of_all _ fun u => by rw [Complex.norm_exp_ofReal_mul_I])
  have him_μ : (∫ u : ℝ, Complex.exp (((t * (u - a) : ℝ) : ℂ) * Complex.I) ∂μ).im =
      ∫ u : ℝ, Real.sin (t * (u - a)) ∂μ := by
    have h := (Complex.imCLM.integral_comp_comm (hE_int μ)).symm
    simp only [Complex.imCLM_apply, Complex.exp_ofReal_mul_I_im] at h
    exact h
  have him_ν : (∫ u : ℝ, Complex.exp (((t * (u - a) : ℝ) : ℂ) * Complex.I) ∂ν).im =
      ∫ u : ℝ, Real.sin (t * (u - a)) ∂ν := by
    have h := (Complex.imCLM.integral_comp_comm (hE_int ν)).symm
    simp only [Complex.imCLM_apply, Complex.exp_ofReal_mul_I_im] at h
    exact h
  have him : ((∫ u : ℝ, Complex.exp (((t * (u - a) : ℝ) : ℂ) * Complex.I) ∂μ) -
      (∫ u : ℝ, Complex.exp (((t * (u - a) : ℝ) : ℂ) * Complex.I) ∂ν)).im =
      (∫ u : ℝ, Real.sin (t * (u - a)) ∂μ) -
        (∫ u : ℝ, Real.sin (t * (u - a)) ∂ν) := by
    rw [Complex.sub_im, him_μ, him_ν]
  rw [← him]
  exact (Complex.abs_im_le_norm _).trans (norm_integral_exp_sub_shift_le a ht)

lemma integral_one_sub_cos_two_pi_le {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hν : ν (univ \ range (Int.cast : ℤ → ℝ)) = 0) {ε : ℝ}
    (h0 : ‖(∫ u : ℝ, Complex.exp (Complex.I * ((0 : ℝ) : ℂ) * (u : ℂ)) ∂μ) -
      (∫ u : ℝ, Complex.exp (Complex.I * ((0 : ℝ) : ℂ) * (u : ℂ)) ∂ν)‖ ≤ ε)
    (h2pi : ‖(∫ u : ℝ, Complex.exp (Complex.I * ((2 * π : ℝ) : ℂ) * (u : ℂ)) ∂μ) -
      (∫ u : ℝ, Complex.exp (Complex.I * ((2 * π : ℝ) : ℂ) * (u : ℂ)) ∂ν)‖ ≤ ε) :
    ∫ u : ℝ, (1 - Real.cos (2 * π * u)) ∂μ ≤ 2 * ε := by
  have hc0 := abs_integral_cos_sub_le 0 h0
  simp only [sub_zero, zero_mul, Real.cos_zero] at hc0
  have hc2pi := abs_integral_cos_sub_le 0 h2pi
  simp only [sub_zero] at hc2pi
  have hν_zero : ∫ u : ℝ, (1 - Real.cos (2 * π * u)) ∂ν = 0 := by
    refine integral_eq_zero_of_forall_int_eq_zero hν (fun n => ?_)
    rw [cos_two_pi_mul_intCast, sub_self]
  have hint_one : ∀ ρ : Measure ℝ, [IsFiniteMeasure ρ] →
      Integrable (fun _ : ℝ => (1 : ℝ)) ρ :=
    fun ρ _ => integrable_const 1
  have hint_cos : ∀ ρ : Measure ℝ, [IsFiniteMeasure ρ] →
      Integrable (fun u : ℝ => Real.cos (2 * π * u)) ρ :=
    fun ρ _ => integrable_of_continuous_bounded
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))
      (fun u => Real.abs_cos_le_one (2 * π * u))
  have hμ_sub : ∫ u : ℝ, (1 - Real.cos (2 * π * u)) ∂μ =
      (∫ _ : ℝ, (1 : ℝ) ∂μ) - ∫ u : ℝ, Real.cos (2 * π * u) ∂μ :=
    integral_sub (hint_one μ) (hint_cos μ)
  have hν_sub : ∫ u : ℝ, (1 - Real.cos (2 * π * u)) ∂ν =
      (∫ _ : ℝ, (1 : ℝ) ∂ν) - ∫ u : ℝ, Real.cos (2 * π * u) ∂ν :=
    integral_sub (hint_one ν) (hint_cos ν)
  linarith [abs_le.mp hc0, abs_le.mp hc2pi]

lemma eight_mul_integral_distInt_sq_le {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hν : ν (univ \ range (Int.cast : ℤ → ℝ)) = 0) {ε : ℝ}
    (h0 : ‖(∫ u : ℝ, Complex.exp (Complex.I * ((0 : ℝ) : ℂ) * (u : ℂ)) ∂μ) -
      (∫ u : ℝ, Complex.exp (Complex.I * ((0 : ℝ) : ℂ) * (u : ℂ)) ∂ν)‖ ≤ ε)
    (h2pi : ‖(∫ u : ℝ, Complex.exp (Complex.I * ((2 * π : ℝ) : ℂ) * (u : ℂ)) ∂μ) -
      (∫ u : ℝ, Complex.exp (Complex.I * ((2 * π : ℝ) : ℂ) * (u : ℂ)) ∂ν)‖ ≤ ε) :
    8 * ∫ u : ℝ, (distInt u) ^ 2 ∂μ ≤ 2 * ε := by
  have hint_dist : Integrable (fun u : ℝ => (distInt u) ^ 2) μ := by
    refine Integrable.of_bound (measurable_distInt.pow_const 2).aestronglyMeasurable
      ((1 / 2) ^ 2) (ae_of_all _ fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (distInt_nonneg u) (distInt_le_half u) 2
  have hint_cos : Integrable (fun u : ℝ => 1 - Real.cos (2 * π * u)) μ :=
    (integrable_const (1 : ℝ)).sub (integrable_of_continuous_bounded
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))
      (fun u => Real.abs_cos_le_one (2 * π * u)))
  calc 8 * ∫ u : ℝ, (distInt u) ^ 2 ∂μ
    = ∫ u : ℝ, 8 * (distInt u) ^ 2 ∂μ := (MeasureTheory.integral_const_mul 8 _).symm
  _ ≤ ∫ u : ℝ, (1 - Real.cos (2 * π * u)) ∂μ :=
      integral_mono (hint_dist.const_mul 8) hint_cos eight_mul_distInt_sq_le
  _ ≤ 2 * ε := integral_one_sub_cos_two_pi_le hν h0 h2pi

lemma integral_intervalIntegral_swap {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    {w : ℝ → ℝ} (hw : Continuous w) {M : ℝ}
    (hwM : ∀ t ∈ Icc (0 : ℝ) (2 * π), |w t| ≤ M)
    {K : ℝ → ℝ → ℝ} (hK : Continuous (Function.uncurry K))
    (hKM : ∀ t u, |K t u| ≤ 1) :
    IntervalIntegrable (fun t => w t * (∫ u : ℝ, K t u ∂ρ)) volume 0 (2 * π) ∧
      ∫ u : ℝ, (∫ t in (0 : ℝ)..(2 * π), w t * K t u) ∂ρ =
        ∫ t in (0 : ℝ)..(2 * π), w t * (∫ u : ℝ, K t u ∂ρ) := by
  let clamp : ℝ → ℝ := fun t => max 0 (min (2 * π) t)
  have hclamp_cont : Continuous clamp :=
    continuous_const.max (continuous_const.min continuous_id)
  have hclamp_mem : ∀ t : ℝ, clamp t ∈ Icc (0 : ℝ) (2 * π) :=
    fun t => ⟨le_max_left _ _, max_le (by positivity) (min_le_left _ _)⟩
  have hclamp_eq : ∀ {t : ℝ}, t ∈ Ioc (0 : ℝ) (2 * π) → clamp t = t := by
    intro t ht
    simp [clamp, min_eq_right ht.2, max_eq_right ht.1.le]
  let G : ℝ → ℝ → ℝ := fun t u => w (clamp t) * K t u
  have hG_lhs : ∀ u : ℝ, ∫ t in (0 : ℝ)..(2 * π), w t * K t u =
      ∫ t in Ioc (0 : ℝ) (2 * π), G t u := by
    intro u
    rw [intervalIntegral.integral_of_le (by positivity)]
    exact setIntegral_congr_fun measurableSet_Ioc (fun t ht => by simp [G, hclamp_eq ht])
  let μ_t : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (2 * π))
  have : IsFiniteMeasure μ_t := isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  have hG_cont : Continuous (Function.uncurry G) :=
    (hw.comp (hclamp_cont.comp continuous_fst)).mul hK
  have hG_int : Integrable (Function.uncurry G) (μ_t.prod ρ) := by
    refine Integrable.of_bound hG_cont.aestronglyMeasurable (max 0 M) (ae_of_all _ fun p => ?_)
    change ‖w (clamp p.1) * K p.1 p.2‖ ≤ max 0 M
    rw [Real.norm_eq_abs, abs_mul]
    calc |w (clamp p.1)| * |K p.1 p.2|
      ≤ |w (clamp p.1)| * 1 := mul_le_mul_of_nonneg_left (hKM p.1 p.2) (abs_nonneg _)
    _ = |w (clamp p.1)| := mul_one _
    _ ≤ M := hwM (clamp p.1) (hclamp_mem p.1)
    _ ≤ max 0 M := le_max_right 0 M
  refine ⟨?_, ?_⟩
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)]
    refine hG_int.integral_prod_left.congr (ae_restrict_of_forall_mem measurableSet_Ioc ?_)
    intro t ht
    simp only [Function.uncurry_apply_pair, G, hclamp_eq ht, MeasureTheory.integral_const_mul]
  · simp_rw [hG_lhs]
    change ∫ u : ℝ, (∫ t : ℝ, G t u ∂μ_t) ∂ρ =
      ∫ t in (0 : ℝ)..(2 * π), w t * (∫ u : ℝ, K t u ∂ρ)
    rw [← MeasureTheory.integral_integral_swap hG_int,
      intervalIntegral.integral_of_le (by positivity)]
    refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    simp only [G, hclamp_eq ht, MeasureTheory.integral_const_mul]

lemma abs_integral_fejerKernel_sub_le {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {ε : ℝ} (_hε : 0 ≤ ε) (a : ℝ)
    (h_four : ∀ t ∈ Icc (0 : ℝ) (2 * π),
      ‖(∫ u : ℝ, Complex.exp (Complex.I * (t : ℂ) * (u : ℂ)) ∂μ) -
        (∫ u : ℝ, Complex.exp (Complex.I * (t : ℂ) * (u : ℂ)) ∂ν)‖ ≤ ε) :
    |(∫ u : ℝ, fejerKernel (u - a) ∂μ) -
      (∫ u : ℝ, fejerKernel (u - a) ∂ν)| ≤ ε := by
  have hswap : ∀ ρ : Measure ℝ, [IsFiniteMeasure ρ] →
      IntervalIntegrable (fun t => (2 * π - t) * (∫ u : ℝ, Real.cos (t * (u - a)) ∂ρ))
        volume 0 (2 * π) ∧
      ∫ u : ℝ, fejerKernel (u - a) ∂ρ =
        (2 * π ^ 2)⁻¹ * ∫ t in (0 : ℝ)..(2 * π),
          (2 * π - t) * (∫ u : ℝ, Real.cos (t * (u - a)) ∂ρ) := by
    intro ρ _
    have h := integral_intervalIntegral_swap (ρ := ρ) (w := fun t => 2 * π - t)
      (continuous_const.sub continuous_id)
      (M := 2 * π) (fun t ht => by rw [abs_of_nonneg (sub_nonneg.mpr ht.2)]; linarith [ht.1])
      (K := fun t u => Real.cos (t * (u - a)))
      (Real.continuous_cos.comp (continuous_fst.mul (continuous_snd.sub continuous_const)))
      (fun t u => Real.abs_cos_le_one _)
    refine ⟨h.1, ?_⟩
    unfold fejerKernel
    rw [MeasureTheory.integral_const_mul, h.2]
  rw [(hswap μ).2, (hswap ν).2, ← mul_sub,
    ← intervalIntegral.integral_sub (hswap μ).1 (hswap ν).1]
  simp_rw [← mul_sub]
  rw [abs_mul, abs_of_pos (by positivity), ← Real.norm_eq_abs]
  have hint_sub : IntervalIntegrable
      (fun t => (2 * π - t) *
        ((∫ u : ℝ, Real.cos (t * (u - a)) ∂μ) - ∫ u : ℝ, Real.cos (t * (u - a)) ∂ν))
      volume 0 (2 * π) := by
    simpa [mul_sub] using (hswap μ).1.sub (hswap ν).1
  have hnorm : ‖∫ t in (0 : ℝ)..(2 * π), (2 * π - t) *
      ((∫ u : ℝ, Real.cos (t * (u - a)) ∂μ) -
        ∫ u : ℝ, Real.cos (t * (u - a)) ∂ν)‖ ≤
      ∫ t in (0 : ℝ)..(2 * π), (2 * π - t) * ε := by
    refine (intervalIntegral.norm_integral_le_integral_norm (by positivity)).trans
      (intervalIntegral.integral_mono_on (by positivity) hint_sub.norm
        (((continuous_const.sub continuous_id).mul continuous_const).intervalIntegrable 0 (2 * π))
        (fun t ht => ?_))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.mpr ht.2)]
    exact mul_le_mul_of_nonneg_left (abs_integral_cos_sub_le a (h_four t ht))
      (sub_nonneg.mpr ht.2)
  have hint_val : ∫ t in (0 : ℝ)..(2 * π), (2 * π - t) * ε = 2 * π ^ 2 * ε := by
    rw [intervalIntegral.integral_mul_const, integral_two_pi_sub]
  rw [hint_val] at hnorm
  have hpi : 0 < 2 * π ^ 2 := by positivity
  calc (2 * π ^ 2)⁻¹ *
      ‖∫ t in (0 : ℝ)..(2 * π), (2 * π - t) *
        ((∫ u : ℝ, Real.cos (t * (u - a)) ∂μ) - ∫ u : ℝ, Real.cos (t * (u - a)) ∂ν)‖
    ≤ (2 * π ^ 2)⁻¹ * (2 * π ^ 2 * ε) := mul_le_mul_of_nonneg_left hnorm (by positivity)
  _ = ε := by field_simp

lemma abs_integral_fejerSlopeKernel_sub_le {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {ε : ℝ} (_hε : 0 ≤ ε) (a : ℝ)
    (h_four : ∀ t ∈ Icc (0 : ℝ) (2 * π),
      ‖(∫ u : ℝ, Complex.exp (Complex.I * (t : ℂ) * (u : ℂ)) ∂μ) -
        (∫ u : ℝ, Complex.exp (Complex.I * (t : ℂ) * (u : ℂ)) ∂ν)‖ ≤ ε) :
    |(∫ u : ℝ, fejerSlopeKernel (u - a) ∂μ) -
      (∫ u : ℝ, fejerSlopeKernel (u - a) ∂ν)| ≤ ε / π := by
  have hswap : ∀ ρ : Measure ℝ, [IsFiniteMeasure ρ] →
      IntervalIntegrable (fun t => 1 * (∫ u : ℝ, Real.sin (t * (u - a)) ∂ρ))
        volume 0 (2 * π) ∧
      ∫ u : ℝ, fejerSlopeKernel (u - a) ∂ρ =
        (2 * π ^ 2)⁻¹ * ∫ t in (0 : ℝ)..(2 * π),
          1 * (∫ u : ℝ, Real.sin (t * (u - a)) ∂ρ) := by
    intro ρ _
    have h := integral_intervalIntegral_swap (ρ := ρ) (w := fun _ => (1 : ℝ)) continuous_const
      (M := 1) (fun _ _ => by norm_num)
      (K := fun t u => Real.sin (t * (u - a)))
      (Real.continuous_sin.comp (continuous_fst.mul (continuous_snd.sub continuous_const)))
      (fun t u => Real.abs_sin_le_one _)
    refine ⟨h.1, ?_⟩
    unfold fejerSlopeKernel
    rw [MeasureTheory.integral_const_mul, h.2]
  rw [(hswap μ).2, (hswap ν).2, ← mul_sub,
    ← intervalIntegral.integral_sub (hswap μ).1 (hswap ν).1]
  simp_rw [← mul_sub]
  rw [abs_mul, abs_of_pos (by positivity), ← Real.norm_eq_abs]
  have hint_sub : IntervalIntegrable
      (fun t => 1 *
        ((∫ u : ℝ, Real.sin (t * (u - a)) ∂μ) - ∫ u : ℝ, Real.sin (t * (u - a)) ∂ν))
      volume 0 (2 * π) := by
    simpa [mul_sub] using (hswap μ).1.sub (hswap ν).1
  have hnorm : ‖∫ t in (0 : ℝ)..(2 * π), 1 *
      ((∫ u : ℝ, Real.sin (t * (u - a)) ∂μ) -
        ∫ u : ℝ, Real.sin (t * (u - a)) ∂ν)‖ ≤
      ∫ _t in (0 : ℝ)..(2 * π), ε := by
    refine (intervalIntegral.norm_integral_le_integral_norm (by positivity)).trans
      (intervalIntegral.integral_mono_on (by positivity) hint_sub.norm
        (continuous_const.intervalIntegrable 0 (2 * π))
        (fun t ht => ?_))
    rw [Real.norm_eq_abs, one_mul]
    exact abs_integral_sin_sub_le a (h_four t ht)
  have hint_val : ∫ _t in (0 : ℝ)..(2 * π), ε = 2 * π * ε := by
    simp [intervalIntegral.integral_const, mul_comm]
  rw [hint_val] at hnorm
  have hpi : π ≠ 0 := Real.pi_ne_zero
  calc (2 * π ^ 2)⁻¹ *
      ‖∫ t in (0 : ℝ)..(2 * π), 1 *
        ((∫ u : ℝ, Real.sin (t * (u - a)) ∂μ) - ∫ u : ℝ, Real.sin (t * (u - a)) ∂ν)‖
    ≤ (2 * π ^ 2)⁻¹ * (2 * π * ε) := mul_le_mul_of_nonneg_left hnorm (by positivity)
  _ = ε / π := by field_simp

/-! ## 5. Second-Order Mean Value Remainder Bound at Nearest Integer -/

lemma abs_sub_le_of_mem_uIcc {a b x : ℝ} (hx : x ∈ uIcc a b) :
    |x - a| ≤ |b - a| := by
  rcases le_total a b with hab | hab
  · rw [uIcc_of_le hab] at hx
    rw [abs_of_nonneg (sub_nonneg.mpr hx.1), abs_of_nonneg (sub_nonneg.mpr hab)]
    linarith [hx.2]
  · rw [uIcc_of_ge hab] at hx
    rw [abs_of_nonpos (sub_nonpos.mpr hx.2), abs_of_nonpos (sub_nonpos.mpr hab)]
    linarith [hx.1]

lemma abs_le_mul_distInt_sq_of_vanish_on_int {R R' R'' : ℝ → ℝ}
    {M₂ : ℝ} (hM₂ : 0 ≤ M₂)
    (hR : ∀ x, HasDerivAt R (R' x) x) (hR' : ∀ x, HasDerivAt R' (R'' x) x)
    (hR'' : ∀ x, |R'' x| ≤ M₂)
    (hR_int : ∀ n : ℤ, R n = 0) (hR'_int : ∀ n : ℤ, R' n = 0) (u : ℝ) :
    |R u| ≤ M₂ * (distInt u) ^ 2 := by
  let a : ℝ := (round u : ℝ)
  let s : Set ℝ := uIcc a u
  have hs : Convex ℝ s := convex_uIcc a u
  have ha : a ∈ s := left_mem_uIcc
  have hu : u ∈ s := right_mem_uIcc
  have hR'_bound : ∀ x ∈ s, ‖R' x‖ ≤ M₂ * distInt u := by
    intro x hx
    have hstep := hs.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y _ => (hR' y).hasDerivWithinAt)
      (fun y _ => by simpa [Real.norm_eq_abs] using hR'' y) ha hx
    rw [hR'_int (round u), sub_zero] at hstep
    refine hstep.trans (mul_le_mul_of_nonneg_left ?_ hM₂)
    simpa [Real.norm_eq_abs, distInt, a] using abs_sub_le_of_mem_uIcc hx
  have hstep2 := hs.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y _ => (hR y).hasDerivWithinAt) hR'_bound ha hu
  rw [hR_int (round u), sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hstep2
  calc |R u| ≤ (M₂ * distInt u) * |u - a| := hstep2
  _ = M₂ * (distInt u) ^ 2 := by unfold distInt a; ring

/-! ## 6. Fejér–Hermite Interpolant and Main Measure Estimate -/

/-- The finite Fejér–Hermite interpolant of `ψ` on `[-N, N] ∩ ℤ`. -/
noncomputable def hermiteInterp (N : ℕ) (ψ : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    (ψ n * fejerKernel (u - n) + deriv ψ n * fejerSlopeKernel (u - n))

/-- First derivative of `hermiteInterp N ψ`. -/
noncomputable def hermiteInterpDeriv (N : ℕ) (ψ : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    (ψ n * fejerKernelDeriv (u - n) + deriv ψ n * fejerSlopeKernelDeriv (u - n))

/-- Second derivative of `hermiteInterp N ψ`. -/
noncomputable def hermiteInterpDeriv2 (N : ℕ) (ψ : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    (ψ n * fejerKernelDeriv2 (u - n) + deriv ψ n * fejerSlopeKernelDeriv2 (u - n))

lemma hasDerivAt_hermiteInterp (N : ℕ) (ψ : ℝ → ℝ) (u : ℝ) :
    HasDerivAt (hermiteInterp N ψ) (hermiteInterpDeriv N ψ u) u := by
  have h := HasDerivAt.sum (u := Finset.Icc (-(N : ℤ)) (N : ℤ))
    (A := fun (n : ℤ) (x : ℝ) =>
      ψ n * fejerKernel (x - n) + deriv ψ n * fejerSlopeKernel (x - n))
    (A' := fun (n : ℤ) =>
      ψ n * fejerKernelDeriv (u - n) + deriv ψ n * fejerSlopeKernelDeriv (u - n))
    (x := u) (fun n _ => ?_)
  · convert h using 1
    · ext x
      simp [hermiteInterp, Finset.sum_apply]
    · rfl
  · have hsub : HasDerivAt (fun x : ℝ => x - (n : ℝ)) 1 u :=
      (hasDerivAt_id u).sub_const (n : ℝ)
    have h1 : HasDerivAt (fun x : ℝ => ψ n * fejerKernel (x - n))
        (ψ n * fejerKernelDeriv (u - n)) u := by
      simpa [mul_one] using ((hasDerivAt_fejerKernel (u - n)).comp u hsub).const_mul (ψ n)
    have h2 : HasDerivAt (fun x : ℝ => deriv ψ n * fejerSlopeKernel (x - n))
        (deriv ψ n * fejerSlopeKernelDeriv (u - n)) u := by
      simpa [mul_one] using
        ((hasDerivAt_fejerSlopeKernel (u - n)).comp u hsub).const_mul (deriv ψ n)
    exact h1.add h2

lemma hasDerivAt_hermiteInterpDeriv (N : ℕ) (ψ : ℝ → ℝ) (u : ℝ) :
    HasDerivAt (hermiteInterpDeriv N ψ) (hermiteInterpDeriv2 N ψ u) u := by
  have h := HasDerivAt.sum (u := Finset.Icc (-(N : ℤ)) (N : ℤ))
    (A := fun (n : ℤ) (x : ℝ) =>
      ψ n * fejerKernelDeriv (x - n) + deriv ψ n * fejerSlopeKernelDeriv (x - n))
    (A' := fun (n : ℤ) =>
      ψ n * fejerKernelDeriv2 (u - n) + deriv ψ n * fejerSlopeKernelDeriv2 (u - n))
    (x := u) (fun n _ => ?_)
  · convert h using 1
    · ext x
      simp [hermiteInterpDeriv, Finset.sum_apply]
    · rfl
  · have hsub : HasDerivAt (fun x : ℝ => x - (n : ℝ)) 1 u :=
      (hasDerivAt_id u).sub_const (n : ℝ)
    have h1 : HasDerivAt (fun x : ℝ => ψ n * fejerKernelDeriv (x - n))
        (ψ n * fejerKernelDeriv2 (u - n)) u := by
      simpa [mul_one] using ((hasDerivAt_fejerKernelDeriv (u - n)).comp u hsub).const_mul (ψ n)
    have h2 : HasDerivAt (fun x : ℝ => deriv ψ n * fejerSlopeKernelDeriv (x - n))
        (deriv ψ n * fejerSlopeKernelDeriv2 (u - n)) u := by
      simpa [mul_one] using
        ((hasDerivAt_fejerSlopeKernelDeriv (u - n)).comp u hsub).const_mul (deriv ψ n)
    exact h1.add h2

lemma deriv_eq_zero_of_support {N : ℕ} {ψ : ℝ → ℝ}
    (hsupp : ∀ u : ℝ, (N : ℝ) < |u| → ψ u = 0) {u : ℝ} (hu : (N : ℝ) < |u|) :
    deriv ψ u = 0 := by
  have hev : ψ =ᶠ[𝓝 u] (fun _ => (0 : ℝ)) := by
    have hopen : IsOpen {x : ℝ | (N : ℝ) < |x|} :=
      isOpen_lt continuous_const continuous_abs
    filter_upwards [hopen.mem_nhds hu] with x hx
    exact hsupp x hx
  rw [hev.deriv_eq, deriv_const]

lemma hermiteInterp_intCast {N : ℕ} {ψ : ℝ → ℝ}
    (hsupp : ∀ u : ℝ, (N : ℝ) < |u| → ψ u = 0) (m : ℤ) :
    hermiteInterp N ψ (m : ℝ) = ψ (m : ℝ) := by
  unfold hermiteInterp
  have hterm : ∀ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      ψ n * fejerKernel ((m : ℝ) - n) + deriv ψ n * fejerSlopeKernel ((m : ℝ) - n) =
        if n = m then ψ (m : ℝ) else 0 := by
    intro n _
    have hsub : (m : ℝ) - (n : ℝ) = ((m - n : ℤ) : ℝ) := (Int.cast_sub m n).symm
    rw [hsub, fejerSlopeKernel_intCast, mul_zero, add_zero]
    split_ifs with hnm
    · subst hnm
      simp
    · rw [fejerKernel_intCast_of_ne_zero (sub_ne_zero.mpr (Ne.symm hnm)), mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · simp only [Finset.mem_Icc, not_and_or, not_le] at hm
    symm
    refine hsupp (m : ℝ) ?_
    rw [← Int.cast_abs, ← Int.cast_natCast, Int.cast_lt]
    rcases hm with h1 | h2
    · exact lt_of_lt_of_le (by omega) (neg_le_abs m)
    · exact lt_of_lt_of_le h2 (le_abs_self m)

lemma hermiteInterpDeriv_intCast {N : ℕ} {ψ : ℝ → ℝ}
    (hsupp : ∀ u : ℝ, (N : ℝ) < |u| → ψ u = 0) (m : ℤ) :
    hermiteInterpDeriv N ψ (m : ℝ) = deriv ψ (m : ℝ) := by
  unfold hermiteInterpDeriv
  have hterm : ∀ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      ψ n * fejerKernelDeriv ((m : ℝ) - n) + deriv ψ n * fejerSlopeKernelDeriv ((m : ℝ) - n) =
        if n = m then deriv ψ (m : ℝ) else 0 := by
    intro n _
    have hsub : (m : ℝ) - (n : ℝ) = ((m - n : ℤ) : ℝ) := (Int.cast_sub m n).symm
    rw [hsub, fejerKernelDeriv_intCast, mul_zero, zero_add]
    split_ifs with hnm
    · subst hnm
      simp
    · rw [fejerSlopeKernelDeriv_intCast_of_ne_zero (sub_ne_zero.mpr (Ne.symm hnm)), mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · simp only [Finset.mem_Icc, not_and_or, not_le] at hm
    symm
    refine deriv_eq_zero_of_support hsupp ?_
    rw [← Int.cast_abs, ← Int.cast_natCast, Int.cast_lt]
    rcases hm with h1 | h2
    · exact lt_of_lt_of_le (by omega) (neg_le_abs m)
    · exact lt_of_lt_of_le h2 (le_abs_self m)

lemma card_Icc_neg_int_cast (N : ℕ) :
    ((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℝ) = 2 * (N : ℝ) + 1 := by
  rw [Int.card_Icc]
  have h : (N : ℤ) + 1 - -(N : ℤ) = ((2 * N + 1 : ℕ) : ℤ) := by omega
  rw [h, Int.toNat_natCast]
  push_cast
  ring

lemma abs_hermiteInterpDeriv2_le (N : ℕ) {ψ : ℝ → ℝ} {M_ψ : ℝ} (hM : 0 ≤ M_ψ)
    (hψ0 : ∀ u, |ψ u| ≤ M_ψ) (hψ1 : ∀ u, |deriv ψ u| ≤ M_ψ) (u : ℝ) :
    |hermiteInterpDeriv2 N ψ u| ≤
      (2 * (N : ℝ) + 1) * (2 * π ^ 2 / 3 + 4 * π / 3) * M_ψ := by
  unfold hermiteInterpDeriv2
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      |ψ n * fejerKernelDeriv2 (u - n) + deriv ψ n * fejerSlopeKernelDeriv2 (u - n)| ≤
        (2 * π ^ 2 / 3 + 4 * π / 3) * M_ψ := by
    intro n _
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 : |ψ n| * |fejerKernelDeriv2 (u - n)| ≤ M_ψ * (2 * π ^ 2 / 3) :=
      mul_le_mul (hψ0 n) (abs_fejerKernelDeriv2_le (u - n)) (abs_nonneg _) hM
    have h2 : |deriv ψ n| * |fejerSlopeKernelDeriv2 (u - n)| ≤ M_ψ * (4 * π / 3) :=
      mul_le_mul (hψ1 n) (abs_fejerSlopeKernelDeriv2_le (u - n)) (abs_nonneg _) hM
    linarith
  calc ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      |ψ n * fejerKernelDeriv2 (u - n) + deriv ψ n * fejerSlopeKernelDeriv2 (u - n)|
    ≤ ∑ _n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (2 * π ^ 2 / 3 + 4 * π / 3) * M_ψ :=
      Finset.sum_le_sum hterm
  _ = (2 * (N : ℝ) + 1) * (2 * π ^ 2 / 3 + 4 * π / 3) * M_ψ := by
      rw [Finset.sum_const, nsmul_eq_mul, card_Icc_neg_int_cast, mul_assoc]

lemma abs_integral_hermiteInterp_sub_le {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (N : ℕ) {ψ : ℝ → ℝ} {M_ψ ε : ℝ} (hM : 0 ≤ M_ψ) (hε : 0 ≤ ε)
    (hψ0 : ∀ u, |ψ u| ≤ M_ψ) (hψ1 : ∀ u, |deriv ψ u| ≤ M_ψ)
    (h_four : ∀ t ∈ Icc (0 : ℝ) (2 * π),
      ‖(∫ u : ℝ, Complex.exp (Complex.I * (t : ℂ) * (u : ℂ)) ∂μ) -
        (∫ u : ℝ, Complex.exp (Complex.I * (t : ℂ) * (u : ℂ)) ∂ν)‖ ≤ ε) :
    |(∫ u : ℝ, hermiteInterp N ψ u ∂μ) - (∫ u : ℝ, hermiteInterp N ψ u ∂ν)| ≤
      (2 * (N : ℝ) + 1) * (1 + 1 / π) * ε * M_ψ := by
  have hint_K : ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ] (n : ℤ),
      Integrable (fun u : ℝ => ψ n * fejerKernel (u - n)) ρ :=
    fun ρ _ n => (integrable_of_continuous_bounded
      (continuous_fejerKernel.comp (continuous_id.sub continuous_const))
      (fun u => abs_fejerKernel_le_one (u - n))).const_mul (ψ n)
  have hint_S : ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ] (n : ℤ),
      Integrable (fun u : ℝ => deriv ψ n * fejerSlopeKernel (u - n)) ρ :=
    fun ρ _ n => (integrable_of_continuous_bounded
      (continuous_fejerSlopeKernel.comp (continuous_id.sub continuous_const))
      (fun u => abs_fejerSlopeKernel_le (u - n))).const_mul (deriv ψ n)
  have hint_KS : ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ] (n : ℤ),
      Integrable (fun u : ℝ => ψ n * fejerKernel (u - n) +
        deriv ψ n * fejerSlopeKernel (u - n)) ρ :=
    fun ρ _ n => (hint_K ρ n).add (hint_S ρ n)
  have hsum : ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ],
      ∫ u : ℝ, hermiteInterp N ψ u ∂ρ =
        ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          (ψ n * (∫ u : ℝ, fejerKernel (u - n) ∂ρ) +
            deriv ψ n * (∫ u : ℝ, fejerSlopeKernel (u - n) ∂ρ)) := by
    intro ρ _
    unfold hermiteInterp
    rw [MeasureTheory.integral_finsetSum _ (fun n _ => hint_KS ρ n)]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [integral_add (hint_K ρ n) (hint_S ρ n), MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
  rw [hsum μ, hsum ν, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      |(ψ n * ∫ u : ℝ, fejerKernel (u - n) ∂μ) +
          deriv ψ n * ∫ u : ℝ, fejerSlopeKernel (u - n) ∂μ -
        ((ψ n * ∫ u : ℝ, fejerKernel (u - n) ∂ν) +
          deriv ψ n * ∫ u : ℝ, fejerSlopeKernel (u - n) ∂ν)| ≤
        (1 + 1 / π) * ε * M_ψ := by
    intro n _
    have hrew : (ψ n * ∫ u : ℝ, fejerKernel (u - n) ∂μ) +
          deriv ψ n * ∫ u : ℝ, fejerSlopeKernel (u - n) ∂μ -
        ((ψ n * ∫ u : ℝ, fejerKernel (u - n) ∂ν) +
          deriv ψ n * ∫ u : ℝ, fejerSlopeKernel (u - n) ∂ν) =
      ψ n * ((∫ u : ℝ, fejerKernel (u - n) ∂μ) - ∫ u : ℝ, fejerKernel (u - n) ∂ν) +
        deriv ψ n * ((∫ u : ℝ, fejerSlopeKernel (u - n) ∂μ) -
          ∫ u : ℝ, fejerSlopeKernel (u - n) ∂ν) := by ring
    rw [hrew]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 : |ψ n| *
        |(∫ u : ℝ, fejerKernel (u - n) ∂μ) - ∫ u : ℝ, fejerKernel (u - n) ∂ν| ≤
        M_ψ * ε :=
      mul_le_mul (hψ0 n) (abs_integral_fejerKernel_sub_le hε n h_four) (abs_nonneg _) hM
    have h2 : |deriv ψ n| *
        |(∫ u : ℝ, fejerSlopeKernel (u - n) ∂μ) -
          ∫ u : ℝ, fejerSlopeKernel (u - n) ∂ν| ≤
        M_ψ * (ε / π) :=
      mul_le_mul (hψ1 n) (abs_integral_fejerSlopeKernel_sub_le hε n h_four) (abs_nonneg _) hM
    have h3 : M_ψ * ε + M_ψ * (ε / π) = (1 + 1 / π) * ε * M_ψ := by ring
    linarith
  calc ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      |(ψ n * ∫ u : ℝ, fejerKernel (u - n) ∂μ) +
          deriv ψ n * ∫ u : ℝ, fejerSlopeKernel (u - n) ∂μ -
        ((ψ n * ∫ u : ℝ, fejerKernel (u - n) ∂ν) +
          deriv ψ n * ∫ u : ℝ, fejerSlopeKernel (u - n) ∂ν)|
    ≤ ∑ _n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (1 + 1 / π) * ε * M_ψ :=
      Finset.sum_le_sum hterm
  _ = (2 * (N : ℝ) + 1) * (1 + 1 / π) * ε * M_ψ := by
      rw [Finset.sum_const, nsmul_eq_mul, card_Icc_neg_int_cast]
      ring

/-- Explicit constant `C_N > 0` for the Fejér–Hermite measure estimate on `[-N, N]`. -/
noncomputable def hermiteConstant (N : ℕ) : ℝ :=
  (2 * (N : ℝ) + 1) * (1 + 1 / π) +
    (1 + (2 * (N : ℝ) + 1) * (2 * π ^ 2 / 3 + 4 * π / 3)) / 4

lemma hermiteConstant_pos (N : ℕ) : 0 < hermiteConstant N := by
  unfold hermiteConstant
  positivity

/-- **Fejér–Hermite Measure Estimate on `ℤ`**:
If `μ, ν` are finite positive measures on `ℝ` with `ν` supported on `ℤ` whose Fourier
transforms differ by at most `ε` on `[0, 2π]`, then for any twice-differentiable function
`ψ : ℝ → ℝ` supported in `[-N, N]` with `|ψ|, |ψ'|, |ψ''| ≤ M_ψ`, the integrals of `ψ`
against `μ` and `ν` differ by at most `hermiteConstant N * ε * M_ψ`. -/
theorem abs_integral_sub_le_of_fourier_bound {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hν : ν (univ \ range (Int.cast : ℤ → ℝ)) = 0)
    (N : ℕ) {ψ : ℝ → ℝ} (hψ_diff : Differentiable ℝ ψ)
    (hψ'_diff : Differentiable ℝ (deriv ψ))
    (hsupp : ∀ u : ℝ, (N : ℝ) < |u| → ψ u = 0)
    {M_ψ ε : ℝ} (hM : 0 ≤ M_ψ) (hε : 0 ≤ ε)
    (hψ0 : ∀ u, |ψ u| ≤ M_ψ) (hψ1 : ∀ u, |deriv ψ u| ≤ M_ψ)
    (hψ2 : ∀ u, |deriv (deriv ψ) u| ≤ M_ψ)
    (h_four : ∀ t ∈ Icc (0 : ℝ) (2 * π),
      ‖(∫ u : ℝ, Complex.exp (Complex.I * (t : ℂ) * (u : ℂ)) ∂μ) -
        (∫ u : ℝ, Complex.exp (Complex.I * (t : ℂ) * (u : ℂ)) ∂ν)‖ ≤ ε) :
    |(∫ u : ℝ, ψ u ∂μ) - (∫ u : ℝ, ψ u ∂ν)| ≤ hermiteConstant N * ε * M_ψ := by
  let H : ℝ → ℝ := hermiteInterp N ψ
  let H' : ℝ → ℝ := hermiteInterpDeriv N ψ
  let H'' : ℝ → ℝ := hermiteInterpDeriv2 N ψ
  let R : ℝ → ℝ := fun u => ψ u - H u
  let R' : ℝ → ℝ := fun u => deriv ψ u - H' u
  let R'' : ℝ → ℝ := fun u => deriv (deriv ψ) u - H'' u
  let M₂ : ℝ := (1 + (2 * (N : ℝ) + 1) * (2 * π ^ 2 / 3 + 4 * π / 3)) * M_ψ
  have hM₂_nonneg : 0 ≤ M₂ := by positivity
  have hR_deriv : ∀ u, HasDerivAt R (R' u) u :=
    fun u => (hψ_diff u).hasDerivAt.sub (hasDerivAt_hermiteInterp N ψ u)
  have hR'_deriv : ∀ u, HasDerivAt R' (R'' u) u :=
    fun u => (hψ'_diff u).hasDerivAt.sub (hasDerivAt_hermiteInterpDeriv N ψ u)
  have hR''_bound : ∀ u, |R'' u| ≤ M₂ := by
    intro u
    refine (abs_sub _ _).trans ?_
    have h1 := hψ2 u
    have h2 := abs_hermiteInterpDeriv2_le N hM hψ0 hψ1 u
    dsimp [M₂]
    linarith
  have hR_int : ∀ n : ℤ, R n = 0 := by
    intro n
    simp [R, H, hermiteInterp_intCast hsupp]
  have hR'_int : ∀ n : ℤ, R' n = 0 := by
    intro n
    simp [R', H', hermiteInterpDeriv_intCast hsupp]
  have hR_le : ∀ u : ℝ, |R u| ≤ M₂ * (distInt u) ^ 2 :=
    abs_le_mul_distInt_sq_of_vanish_on_int hM₂_nonneg hR_deriv hR'_deriv
      hR''_bound hR_int hR'_int
  have hψ_int : ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ], Integrable ψ ρ :=
    fun ρ _ => integrable_of_continuous_bounded hψ_diff.continuous hψ0
  have hH_cont : Continuous H :=
    Differentiable.continuous (fun u => (hasDerivAt_hermiteInterp N ψ u).differentiableAt)
  have hH_bound : ∀ u, |H u| ≤ (2 * (N : ℝ) + 1) * (1 + 1 / π) * M_ψ := by
    intro u
    unfold H hermiteInterp
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        |ψ n * fejerKernel (u - n) + deriv ψ n * fejerSlopeKernel (u - n)| ≤
          (1 + 1 / π) * M_ψ := by
      intro n _
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      have h1 : |ψ n| * |fejerKernel (u - n)| ≤ M_ψ * 1 :=
        mul_le_mul (hψ0 n) (abs_fejerKernel_le_one (u - n)) (abs_nonneg _) hM
      have h2 : |deriv ψ n| * |fejerSlopeKernel (u - n)| ≤ M_ψ * (1 / π) :=
        mul_le_mul (hψ1 n) (abs_fejerSlopeKernel_le (u - n)) (abs_nonneg _) hM
      linarith
    calc ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        |ψ n * fejerKernel (u - n) + deriv ψ n * fejerSlopeKernel (u - n)|
      ≤ ∑ _n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (1 + 1 / π) * M_ψ :=
        Finset.sum_le_sum hterm
    _ = (2 * (N : ℝ) + 1) * (1 + 1 / π) * M_ψ := by
        rw [Finset.sum_const, nsmul_eq_mul, card_Icc_neg_int_cast, mul_assoc]
  have hH_int : ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ], Integrable H ρ :=
    fun ρ _ => integrable_of_continuous_bounded hH_cont hH_bound
  have hR_integrable : ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ], Integrable R ρ :=
    fun ρ _ => (hψ_int ρ).sub (hH_int ρ)
  have hR_ν : ∫ u : ℝ, R u ∂ν = 0 :=
    integral_eq_zero_of_forall_int_eq_zero hν hR_int
  have hR_μ : |∫ u : ℝ, R u ∂μ| ≤ (M₂ / 4) * ε := by
    rw [← Real.norm_eq_abs]
    have h1 : ‖∫ u : ℝ, R u ∂μ‖ ≤ ∫ u : ℝ, ‖R u‖ ∂μ :=
      norm_integral_le_integral_norm R
    have hint_dist : Integrable (fun u : ℝ => (distInt u) ^ 2) μ := by
      refine Integrable.of_bound (measurable_distInt.pow_const 2).aestronglyMeasurable
        ((1 / 2) ^ 2) (ae_of_all _ fun u => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (distInt_nonneg u) (distInt_le_half u) 2
    have h2 : ∫ u : ℝ, ‖R u‖ ∂μ ≤ ∫ u : ℝ, M₂ * (distInt u) ^ 2 ∂μ :=
      integral_mono (hR_integrable μ).norm (hint_dist.const_mul M₂)
        (fun u => by simpa [Real.norm_eq_abs] using hR_le u)
    rw [MeasureTheory.integral_const_mul] at h2
    have h0_mem : (0 : ℝ) ∈ Icc (0 : ℝ) (2 * π) := ⟨le_rfl, by positivity⟩
    have h2pi_mem : 2 * π ∈ Icc (0 : ℝ) (2 * π) := ⟨by positivity, le_rfl⟩
    have hdist_int :=
      eight_mul_integral_distInt_sq_le hν (h_four 0 h0_mem) (h_four (2 * π) h2pi_mem)
    have hdist_le : ∫ u : ℝ, (distInt u) ^ 2 ∂μ ≤ ε / 4 := by linarith
    have h3 : M₂ * ∫ u : ℝ, (distInt u) ^ 2 ∂μ ≤ M₂ * (ε / 4) :=
      mul_le_mul_of_nonneg_left hdist_le hM₂_nonneg
    linarith
  have hHR_eq : (fun u => H u + R u) = ψ := by ext u; simp [R]
  have hdecomp_μ : ∫ u : ℝ, ψ u ∂μ =
      (∫ u : ℝ, H u ∂μ) + ∫ u : ℝ, R u ∂μ := by
    have h := integral_add (hH_int μ) (hR_integrable μ)
    rwa [hHR_eq] at h
  have hdecomp_ν : ∫ u : ℝ, ψ u ∂ν = ∫ u : ℝ, H u ∂ν := by
    have h := integral_add (hH_int ν) (hR_integrable ν)
    rw [hHR_eq, hR_ν, add_zero] at h
    exact h
  rw [hdecomp_μ, hdecomp_ν]
  have hrew : (∫ u : ℝ, H u ∂μ) + (∫ u : ℝ, R u ∂μ) - ∫ u : ℝ, H u ∂ν =
      ((∫ u : ℝ, H u ∂μ) - ∫ u : ℝ, H u ∂ν) + ∫ u : ℝ, R u ∂μ := by ring
  rw [hrew]
  refine (abs_add_le _ _).trans ?_
  have hH_diff := abs_integral_hermiteInterp_sub_le N hM hε hψ0 hψ1 h_four
  unfold hermiteConstant
  dsimp [M₂] at hR_μ
  linarith

/-- Version of `abs_integral_sub_le_of_fourier_bound` assuming `ContDiff ℝ 2 ψ` and the
symmetric Fourier window `t ∈ [-2π, 2π]`. -/
theorem abs_integral_sub_le_of_fourier_bound_contDiff {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hν : ν (univ \ range (Int.cast : ℤ → ℝ)) = 0)
    (N : ℕ) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hsupp : ∀ u : ℝ, (N : ℝ) < |u| → ψ u = 0)
    {M_ψ ε : ℝ} (hM : 0 ≤ M_ψ) (hε : 0 ≤ ε)
    (hψ0 : ∀ u, |ψ u| ≤ M_ψ) (hψ1 : ∀ u, |deriv ψ u| ≤ M_ψ)
    (hψ2 : ∀ u, |deriv (deriv ψ) u| ≤ M_ψ)
    (h_four : ∀ t ∈ Icc (-2 * π) (2 * π),
      ‖(∫ u : ℝ, Complex.exp (Complex.I * (t : ℂ) * (u : ℂ)) ∂μ) -
        (∫ u : ℝ, Complex.exp (Complex.I * (t : ℂ) * (u : ℂ)) ∂ν)‖ ≤ ε) :
    |(∫ u : ℝ, ψ u ∂μ) - (∫ u : ℝ, ψ u ∂ν)| ≤ hermiteConstant N * ε * M_ψ := by
  have hψ_diff : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have hψ_succ : ContDiff ℝ (1 + 1) ψ := hψ
  have hψ'_diff : Differentiable ℝ (deriv ψ) :=
    ((contDiff_succ_iff_deriv.mp hψ_succ).2.2).differentiable (by norm_num)
  exact abs_integral_sub_le_of_fourier_bound hν N hψ_diff hψ'_diff hsupp hM hε hψ0 hψ1 hψ2
    (fun t ht => h_four t ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)

end CFT.LightconeBootstrap
