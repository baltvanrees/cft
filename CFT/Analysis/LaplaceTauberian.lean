/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Balt van Rees
-/
import CFT.Analysis.TwoConstants
import CFT.Analysis.HermiteMeasure

/-!
# Quantitative Laplace-to-`C_c^2` Tauberian Theorem on `ℤ`

This file combines Nevanlinna's Two-Constants Theorem on a vertical strip (`TwoConstants.lean`)
with the Fejér–Hermite measure estimate on `ℤ` (`HermiteMeasure.lean`) via exponential tilting
(`Measure.withDensity`) to prove the non-asymptotic and asymptotic Laplace-to-`C_c^2` Tauberian
theorems on `ℤ`.
-/

open MeasureTheory Set Filter Metric Real Complex Topology
open scoped ENNReal

namespace CFT.LightconeBootstrap

/-! ## 1. Complex Laplace Transform on a Vertical Strip -/

/-- The two-sided complex Laplace transform `∫ u, exp(z u) dρ(u)` of a measure `ρ` on `ℝ`. -/
noncomputable def laplaceTransform (ρ : Measure ℝ) (z : ℂ) : ℂ :=
  ∫ u : ℝ, Complex.exp (z * (u : ℂ)) ∂ρ

/-- The real Laplace transform `∫ u, exp(σ u) dρ(u)` of a measure `ρ` on `ℝ`. -/
noncomputable def laplaceTransformReal (ρ : Measure ℝ) (σ : ℝ) : ℝ :=
  ∫ u : ℝ, Real.exp (σ * u) ∂ρ

lemma exp_mul_le_add_of_mem_Icc {σ_minus σ_plus σ : ℝ}
    (hσ : σ ∈ Icc σ_minus σ_plus) (u : ℝ) :
    Real.exp (σ * u) ≤ Real.exp (σ_minus * u) + Real.exp (σ_plus * u) := by
  rcases le_total 0 u with hu | hu
  · have h1 : Real.exp (σ * u) ≤ Real.exp (σ_plus * u) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hσ.2 hu)
    linarith [Real.exp_pos (σ_minus * u)]
  · have h1 : Real.exp (σ * u) ≤ Real.exp (σ_minus * u) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hσ.1 hu)
    linarith [Real.exp_pos (σ_plus * u)]

lemma norm_exp_mul_ofReal (z : ℂ) (u : ℝ) :
    ‖Complex.exp (z * (u : ℂ))‖ = Real.exp (z.re * u) := by
  rw [Complex.norm_exp, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]

lemma norm_exp_mul_ofReal_le_of_re_mem_Icc {σ_minus σ_plus : ℝ} {z : ℂ}
    (hz : z.re ∈ Icc σ_minus σ_plus) (u : ℝ) :
    ‖Complex.exp (z * (u : ℂ))‖ ≤ Real.exp (σ_minus * u) + Real.exp (σ_plus * u) := by
  rw [norm_exp_mul_ofReal]
  exact exp_mul_le_add_of_mem_Icc hz u

lemma norm_mul_exp_le_of_re_sub_le {σ_minus σ_plus δ : ℝ} (hδ : 0 < δ) {z : ℂ}
    (h_minus : σ_minus ≤ z.re - δ) (h_plus : z.re + δ ≤ σ_plus) (u : ℝ) :
    ‖(u : ℂ) * Complex.exp (z * (u : ℂ))‖ ≤
      δ⁻¹ * (Real.exp (σ_minus * u) + Real.exp (σ_plus * u)) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_exp_mul_ofReal]
  have h_abs_u : |u| ≤ δ⁻¹ * Real.exp (|u| * δ) := by
    rw [le_inv_mul_iff₀ hδ]
    linarith [Real.add_one_le_exp (|u| * δ)]
  have h_prod : |u| * Real.exp (z.re * u) ≤ δ⁻¹ * Real.exp (z.re * u + |u| * δ) := by
    calc |u| * Real.exp (z.re * u)
        ≤ (δ⁻¹ * Real.exp (|u| * δ)) * Real.exp (z.re * u) :=
          mul_le_mul_of_nonneg_right h_abs_u (Real.exp_pos _).le
      _ = δ⁻¹ * (Real.exp (z.re * u) * Real.exp (|u| * δ)) := by ring
      _ = δ⁻¹ * Real.exp (z.re * u + |u| * δ) := by rw [← Real.exp_add]
  refine h_prod.trans (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hδ.le))
  rcases le_total 0 u with hu | hu
  · have h_eq : z.re * u + |u| * δ = (z.re + δ) * u := by
      rw [abs_of_nonneg hu]; ring
    rw [h_eq]
    have h_le : Real.exp ((z.re + δ) * u) ≤ Real.exp (σ_plus * u) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h_plus hu)
    linarith [Real.exp_pos (σ_minus * u)]
  · have h_eq : z.re * u + |u| * δ = (z.re - δ) * u := by
      rw [abs_of_nonpos hu]; ring
    rw [h_eq]
    have h_le : Real.exp ((z.re - δ) * u) ≤ Real.exp (σ_minus * u) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right h_minus hu)
    linarith [Real.exp_pos (σ_plus * u)]

lemma integrable_exp_mul_of_mem_Icc {ρ : Measure ℝ} {σ_minus σ_plus σ : ℝ}
    (h_minus : Integrable (fun u => Real.exp (σ_minus * u)) ρ)
    (h_plus : Integrable (fun u => Real.exp (σ_plus * u)) ρ)
    (hσ : σ ∈ Icc σ_minus σ_plus) :
    Integrable (fun u => Real.exp (σ * u)) ρ := by
  have h_cont : Continuous (fun u : ℝ => Real.exp (σ * u)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  refine (h_minus.add h_plus).mono' h_cont.aestronglyMeasurable (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact exp_mul_le_add_of_mem_Icc hσ u

lemma integrable_cexp_mul_of_re_mem_Icc {ρ : Measure ℝ} {σ_minus σ_plus : ℝ}
    (h_minus : Integrable (fun u => Real.exp (σ_minus * u)) ρ)
    (h_plus : Integrable (fun u => Real.exp (σ_plus * u)) ρ)
    {z : ℂ} (hz : z.re ∈ Icc σ_minus σ_plus) :
    Integrable (fun u : ℝ => Complex.exp (z * (u : ℂ))) ρ := by
  have h_cont : Continuous (fun u : ℝ => Complex.exp (z * (u : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  refine (h_minus.add h_plus).mono' h_cont.aestronglyMeasurable
    (ae_of_all _ (norm_exp_mul_ofReal_le_of_re_mem_Icc hz))

theorem continuousOn_laplaceTransform {ρ : Measure ℝ} {σ_minus σ_plus : ℝ}
    (h_minus : Integrable (fun u => Real.exp (σ_minus * u)) ρ)
    (h_plus : Integrable (fun u => Real.exp (σ_plus * u)) ρ) :
    ContinuousOn (laplaceTransform ρ) {z : ℂ | z.re ∈ Icc σ_minus σ_plus} := by
  refine continuousOn_of_dominated
    (bound := fun u => Real.exp (σ_minus * u) + Real.exp (σ_plus * u))
    (fun z _ => (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable)
    (fun z hz => ae_of_all _ (norm_exp_mul_ofReal_le_of_re_mem_Icc hz))
    (h_minus.add h_plus)
    (ae_of_all _ fun u => ?_)
  exact (Complex.continuous_exp.comp (continuous_id.mul continuous_const)).continuousOn

theorem differentiableOn_laplaceTransform {ρ : Measure ℝ} {σ_minus σ_plus : ℝ}
    (h_minus : Integrable (fun u => Real.exp (σ_minus * u)) ρ)
    (h_plus : Integrable (fun u => Real.exp (σ_plus * u)) ρ) :
    DifferentiableOn ℂ (laplaceTransform ρ) {z : ℂ | z.re ∈ Ioo σ_minus σ_plus} := by
  intro z₀ hz₀
  simp only [mem_ofPred_eq, mem_Ioo] at hz₀
  let δ : ℝ := min (z₀.re - σ_minus) (σ_plus - z₀.re) / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    have h1 : 0 < z₀.re - σ_minus := sub_pos.mpr hz₀.1
    have h2 : 0 < σ_plus - z₀.re := sub_pos.mpr hz₀.2
    positivity
  let F : ℂ → ℝ → ℂ := fun z u => Complex.exp (z * (u : ℂ))
  let F' : ℂ → ℝ → ℂ := fun z u => (u : ℂ) * Complex.exp (z * (u : ℂ))
  have hF_meas : ∀ z : ℂ, AEStronglyMeasurable (F z) ρ := fun z =>
    (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable
  have hF'_meas : AEStronglyMeasurable (F' z₀) ρ :=
    (Complex.continuous_ofReal.mul
      (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal))).aestronglyMeasurable
  have h_hasDeriv := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (x₀ := z₀) (s := Metric.ball z₀ δ)
    (bound := fun u => δ⁻¹ * (Real.exp (σ_minus * u) + Real.exp (σ_plus * u)))
    (ball_mem_nhds z₀ hδ)
    (Eventually.of_forall hF_meas)
    (integrable_cexp_mul_of_re_mem_Icc h_minus h_plus ⟨hz₀.1.le, hz₀.2.le⟩)
    hF'_meas
    ?_
    ((h_minus.add h_plus).const_mul δ⁻¹)
    ?_).2
  · exact h_hasDeriv.differentiableAt.differentiableWithinAt
  · refine ae_of_all _ (fun u z hz => ?_)
    have hz_re : |z.re - z₀.re| < δ := by
      have h1 : |z.re - z₀.re| ≤ ‖z - z₀‖ := by
        rw [← Complex.sub_re]
        exact Complex.abs_re_le_norm (z - z₀)
      exact lt_of_le_of_lt h1 (mem_ball_iff_norm.mp hz)
    have h_abs := abs_lt.mp hz_re
    have h_m : σ_minus ≤ z.re - δ := by
      have : δ ≤ (z₀.re - σ_minus) / 2 :=
        div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)
      linarith [h_abs.1]
    have h_p : z.re + δ ≤ σ_plus := by
      have : δ ≤ (σ_plus - z₀.re) / 2 :=
        div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)
      linarith [h_abs.2]
    exact norm_mul_exp_le_of_re_sub_le hδ h_m h_p u
  · refine ae_of_all _ (fun u z _ => ?_)
    have h1 : HasDerivAt (fun w : ℂ => w * (u : ℂ)) (1 * (u : ℂ)) z :=
      (hasDerivAt_id z).mul_const (u : ℂ)
    have h2 := h1.cexp
    convert h2 using 1
    dsimp [F']
    ring

lemma laplaceTransform_ofReal (ρ : Measure ℝ) (σ : ℝ) :
    laplaceTransform ρ (σ : ℂ) = (laplaceTransformReal ρ σ : ℂ) := by
  unfold laplaceTransform laplaceTransformReal
  have h_eq : (fun u : ℝ => Complex.exp ((σ : ℂ) * (u : ℂ))) =
      fun u : ℝ => ((Real.exp (σ * u) : ℝ) : ℂ) := by
    ext u
    rw [← Complex.ofReal_mul, Complex.ofReal_exp]
  rw [h_eq, integral_complex_ofReal]

lemma laplaceTransformReal_nonneg (ρ : Measure ℝ) (σ : ℝ) :
    0 ≤ laplaceTransformReal ρ σ :=
  integral_nonneg (fun u => (Real.exp_pos (σ * u)).le)

lemma norm_laplaceTransform_le_laplaceTransformReal (ρ : Measure ℝ) (σ t : ℝ) :
    ‖laplaceTransform ρ ((σ : ℂ) + (t : ℂ) * I)‖ ≤ laplaceTransformReal ρ σ := by
  unfold laplaceTransform laplaceTransformReal
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  dsimp
  rw [norm_exp_mul_ofReal]
  simp

lemma laplaceTransformReal_le_add_of_mem_Icc {ρ : Measure ℝ} {σ_minus σ_plus σ : ℝ}
    (h_minus : Integrable (fun u => Real.exp (σ_minus * u)) ρ)
    (h_plus : Integrable (fun u => Real.exp (σ_plus * u)) ρ)
    (hσ : σ ∈ Icc σ_minus σ_plus) :
    laplaceTransformReal ρ σ ≤
      laplaceTransformReal ρ σ_minus + laplaceTransformReal ρ σ_plus := by
  unfold laplaceTransformReal
  rw [← integral_add h_minus h_plus]
  exact integral_mono (integrable_exp_mul_of_mem_Icc h_minus h_plus hσ)
    (h_minus.add h_plus) (exp_mul_le_add_of_mem_Icc hσ)

/-! ## 2. Exponentially Tilted Measure and Tilted Test Functions -/

/-- The exponentially tilted measure `dρ_A(u) = exp(-A u) dρ(u)`. -/
noncomputable def tiltedMeasure (A : ℝ) (ρ : Measure ℝ) : Measure ℝ :=
  ρ.withDensity (fun u : ℝ => ENNReal.ofReal (Real.exp (-A * u)))

lemma measurable_ennreal_ofReal_exp_neg_mul (A : ℝ) :
    Measurable (fun u : ℝ => ENNReal.ofReal (Real.exp (-A * u))) :=
  ENNReal.measurable_ofReal.comp
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable

lemma isFiniteMeasure_tiltedMeasure {A : ℝ} {ρ : Measure ℝ}
    (h_int : Integrable (fun u : ℝ => Real.exp (-A * u)) ρ) :
    IsFiniteMeasure (tiltedMeasure A ρ) :=
  isFiniteMeasure_withDensity_ofReal h_int.2

lemma tiltedMeasure_compl_intCast_eq_zero (A : ℝ) {ν : Measure ℝ}
    (hν : ν (univ \ range (Int.cast : ℤ → ℝ)) = 0) :
    tiltedMeasure A ν (univ \ range (Int.cast : ℤ → ℝ)) = 0 :=
  withDensity_absolutelyContinuous ν _ hν

lemma integral_tiltedMeasure_eq_integral_mul (A : ℝ) (ρ : Measure ℝ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E) :
    ∫ u : ℝ, g u ∂(tiltedMeasure A ρ) =
      ∫ u : ℝ, Real.exp (-A * u) • g u ∂ρ := by
  let f : ℝ → NNReal := fun u => Real.toNNReal (Real.exp (-A * u))
  have hf_meas : Measurable f :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.real_toNNReal
  change (∫ u : ℝ, g u ∂ρ.withDensity (fun u => (f u : ℝ≥0∞))) =
    ∫ u : ℝ, Real.exp (-A * u) • g u ∂ρ
  rw [integral_withDensity_eq_integral_smul hf_meas]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  dsimp [f]
  rw [NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_pos _).le]

lemma fourier_tiltedMeasure_eq_laplaceTransform (A : ℝ) (ρ : Measure ℝ) (t : ℝ) :
    ∫ u : ℝ, Complex.exp (I * (t : ℂ) * (u : ℂ)) ∂(tiltedMeasure A ρ) =
      laplaceTransform ρ ((-A : ℂ) + (t : ℂ) * I) := by
  rw [integral_tiltedMeasure_eq_integral_mul]
  unfold laplaceTransform
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  dsimp
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The exponentially tilted test function `ψ(u) = exp(A u) φ(u)`. -/
noncomputable def tiltedTest (A : ℝ) (φ : ℝ → ℝ) (u : ℝ) : ℝ :=
  Real.exp (A * u) * φ u

lemma integral_tiltedTest_tiltedMeasure (A : ℝ) (ρ : Measure ℝ) (φ : ℝ → ℝ) :
    ∫ u : ℝ, tiltedTest A φ u ∂(tiltedMeasure A ρ) = ∫ u : ℝ, φ u ∂ρ := by
  rw [integral_tiltedMeasure_eq_integral_mul]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  dsimp [tiltedTest]
  rw [← mul_assoc, ← Real.exp_add]
  have h_zero : -A * u + A * u = 0 := by ring
  rw [h_zero, Real.exp_zero, one_mul]

lemma tiltedTest_eq_zero_of_support (A : ℝ) {N : ℕ} {f : ℝ → ℝ}
    (hsupp : ∀ u : ℝ, (N : ℝ) < |u| → f u = 0) {u : ℝ} (hu : (N : ℝ) < |u|) :
    tiltedTest A f u = 0 := by
  simp [tiltedTest, hsupp u hu]

lemma abs_tiltedTest_le {A : ℝ} (hA : 0 ≤ A) {N : ℕ} {f : ℝ → ℝ} {M_f : ℝ}
    (hM : 0 ≤ M_f) (hsupp : ∀ u : ℝ, (N : ℝ) < |u| → f u = 0)
    (hf : ∀ u : ℝ, |f u| ≤ M_f) (u : ℝ) :
    |tiltedTest A f u| ≤ Real.exp (A * (N : ℝ)) * M_f := by
  rcases lt_or_ge (N : ℝ) |u| with hu | hu
  · rw [tiltedTest_eq_zero_of_support A hsupp hu, abs_zero]
    positivity
  · unfold tiltedTest
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hu_le : u ≤ (N : ℝ) := (le_abs_self u).trans hu
    have hexp : Real.exp (A * u) ≤ Real.exp (A * (N : ℝ)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu_le hA)
    exact mul_le_mul hexp (hf u) (abs_nonneg _) (Real.exp_pos _).le

lemma hasDerivAt_tiltedTest (A : ℝ) {f : ℝ → ℝ} (hf : Differentiable ℝ f) (u : ℝ) :
    HasDerivAt (tiltedTest A f) (A * tiltedTest A f u + tiltedTest A (deriv f) u) u := by
  unfold tiltedTest
  have h1 : HasDerivAt (fun x : ℝ => A * x) (A * 1) u := (hasDerivAt_id u).const_mul A
  have h2 : HasDerivAt (fun x : ℝ => Real.exp (A * x)) (Real.exp (A * u) * (A * 1)) u := h1.exp
  have h3 := h2.mul (hf u).hasDerivAt
  convert h3 using 1
  ring

lemma differentiable_tiltedTest (A : ℝ) {f : ℝ → ℝ} (hf : Differentiable ℝ f) :
    Differentiable ℝ (tiltedTest A f) :=
  fun u => (hasDerivAt_tiltedTest A hf u).differentiableAt

lemma deriv_tiltedTest (A : ℝ) {f : ℝ → ℝ} (hf : Differentiable ℝ f) :
    deriv (tiltedTest A f) = fun u => A * tiltedTest A f u + tiltedTest A (deriv f) u := by
  ext u
  exact (hasDerivAt_tiltedTest A hf u).deriv

lemma differentiable_deriv_tiltedTest (A : ℝ) {φ : ℝ → ℝ}
    (hφ : Differentiable ℝ φ) (hφ' : Differentiable ℝ (deriv φ)) :
    Differentiable ℝ (deriv (tiltedTest A φ)) := by
  rw [deriv_tiltedTest A hφ]
  exact ((differentiable_tiltedTest A hφ).const_mul A).add (differentiable_tiltedTest A hφ')

lemma deriv2_tiltedTest (A : ℝ) {φ : ℝ → ℝ}
    (hφ : Differentiable ℝ φ) (hφ' : Differentiable ℝ (deriv φ)) (u : ℝ) :
    deriv (deriv (tiltedTest A φ)) u =
      A ^ 2 * tiltedTest A φ u + 2 * A * tiltedTest A (deriv φ) u +
        tiltedTest A (deriv (deriv φ)) u := by
  rw [deriv_tiltedTest A hφ]
  have h1 := (hasDerivAt_tiltedTest A hφ u).const_mul A
  have h2 := hasDerivAt_tiltedTest A hφ' u
  have h3 := (h1.add h2).deriv
  convert h3 using 1
  ring

lemma abs_tiltedTest_le_sq {A : ℝ} (hA : 0 ≤ A) {N : ℕ} {φ : ℝ → ℝ} {M_φ : ℝ}
    (hM : 0 ≤ M_φ) (hsupp : ∀ u : ℝ, (N : ℝ) < |u| → φ u = 0)
    (hφ0 : ∀ u : ℝ, |φ u| ≤ M_φ) (u : ℝ) :
    |tiltedTest A φ u| ≤ (A + 1) ^ 2 * Real.exp (A * (N : ℝ)) * M_φ := by
  have h0 := abs_tiltedTest_le hA hM hsupp hφ0 u
  have hA1 : 1 ≤ (A + 1) ^ 2 := by nlinarith
  have h_nonneg : 0 ≤ Real.exp (A * (N : ℝ)) * M_φ := by positivity
  nlinarith

lemma abs_deriv_tiltedTest_le_sq {A : ℝ} (hA : 0 ≤ A) {N : ℕ} {φ : ℝ → ℝ} {M_φ : ℝ}
    (hφ : Differentiable ℝ φ) (hM : 0 ≤ M_φ)
    (hsupp : ∀ u : ℝ, (N : ℝ) < |u| → φ u = 0)
    (hφ0 : ∀ u : ℝ, |φ u| ≤ M_φ) (hφ1 : ∀ u : ℝ, |deriv φ u| ≤ M_φ) (u : ℝ) :
    |deriv (tiltedTest A φ) u| ≤ (A + 1) ^ 2 * Real.exp (A * (N : ℝ)) * M_φ := by
  rw [deriv_tiltedTest A hφ]
  dsimp
  have hsupp' : ∀ x : ℝ, (N : ℝ) < |x| → deriv φ x = 0 :=
    fun x hx => deriv_eq_zero_of_support hsupp hx
  have h0 := abs_tiltedTest_le hA hM hsupp hφ0 u
  have h1 := abs_tiltedTest_le hA hM hsupp' hφ1 u
  have h_tri : |A * tiltedTest A φ u + tiltedTest A (deriv φ) u| ≤
      A * |tiltedTest A φ u| + |tiltedTest A (deriv φ) u| := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hA]
  have h_nonneg : 0 ≤ Real.exp (A * (N : ℝ)) * M_φ := by positivity
  have h_comb : A * |tiltedTest A φ u| + |tiltedTest A (deriv φ) u| ≤
      (A + 1) * (Real.exp (A * (N : ℝ)) * M_φ) := by nlinarith
  have hA2 : A + 1 ≤ (A + 1) ^ 2 := by nlinarith
  nlinarith

lemma abs_deriv2_tiltedTest_le_sq {A : ℝ} (hA : 0 ≤ A) {N : ℕ} {φ : ℝ → ℝ} {M_φ : ℝ}
    (hφ : Differentiable ℝ φ) (hφ' : Differentiable ℝ (deriv φ)) (hM : 0 ≤ M_φ)
    (hsupp : ∀ u : ℝ, (N : ℝ) < |u| → φ u = 0)
    (hφ0 : ∀ u : ℝ, |φ u| ≤ M_φ) (hφ1 : ∀ u : ℝ, |deriv φ u| ≤ M_φ)
    (hφ2 : ∀ u : ℝ, |deriv (deriv φ) u| ≤ M_φ) (u : ℝ) :
    |deriv (deriv (tiltedTest A φ)) u| ≤ (A + 1) ^ 2 * Real.exp (A * (N : ℝ)) * M_φ := by
  rw [deriv2_tiltedTest A hφ hφ' u]
  have hsupp' : ∀ x : ℝ, (N : ℝ) < |x| → deriv φ x = 0 :=
    fun x hx => deriv_eq_zero_of_support hsupp hx
  have hsupp'' : ∀ x : ℝ, (N : ℝ) < |x| → deriv (deriv φ) x = 0 :=
    fun x hx => deriv_eq_zero_of_support hsupp' hx
  have h0 := abs_tiltedTest_le hA hM hsupp hφ0 u
  have h1 := abs_tiltedTest_le hA hM hsupp' hφ1 u
  have h2 := abs_tiltedTest_le hA hM hsupp'' hφ2 u
  have h2A : 0 ≤ 2 * A := by linarith
  have h_tri1 := abs_add_le (A ^ 2 * tiltedTest A φ u + 2 * A * tiltedTest A (deriv φ) u)
    (tiltedTest A (deriv (deriv φ)) u)
  have h_tri2 := abs_add_le (A ^ 2 * tiltedTest A φ u) (2 * A * tiltedTest A (deriv φ) u)
  have h_abs1 : |A ^ 2 * tiltedTest A φ u| = A ^ 2 * |tiltedTest A φ u| := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg A)]
  have h_abs2 : |2 * A * tiltedTest A (deriv φ) u| = 2 * A * |tiltedTest A (deriv φ) u| := by
    rw [abs_mul, abs_of_nonneg h2A]
  nlinarith

/-! ## 3. Non-Asymptotic and Asymptotic Laplace-to-`C_c^2` Tauberian Theorems -/

/-- **Non-Asymptotic Laplace-to-`C_c^2` Tauberian Theorem on `ℤ`**:
Suppose `1 < A`, `μ, ν` are measures on `ℝ` with `ν` supported on `ℤ`, both `exp((1 - 2A) u)`
and `exp(-u)` are integrable with respect to `μ` and `ν`, and on the real interval
`σ ∈ [1 - 2A, -1]`:
- `laplaceTransformReal μ σ + laplaceTransformReal ν σ ≤ M`,
- `|laplaceTransformReal μ σ - laplaceTransformReal ν σ| ≤ δ` (`0 < δ ≤ M`).
Then for any twice-differentiable test function `φ : ℝ → ℝ` supported in `[-N, N]` with
`|φ|, |φ'|, |φ''| ≤ M_φ`, the integrals of `φ` against `μ` and `ν` satisfy
`|(∫ φ dμ) - (∫ φ dν)| ≤ C_N * (A + 1)^2 * exp(A N) * M^(1 - θ) * δ^θ * M_φ`,
where `θ = midpointHarmonicExp A (2 * π)`. -/
theorem abs_integral_sub_le_of_laplaceReal_bound {A M δ : ℝ}
    (hA : 1 < A) (hδ : 0 < δ) (hδM : δ ≤ M)
    {μ ν : Measure ℝ} (hν : ν (univ \ range (Int.cast : ℤ → ℝ)) = 0)
    (hμ_minus : Integrable (fun u => Real.exp ((1 - 2 * A) * u)) μ)
    (hμ_plus : Integrable (fun u => Real.exp ((-1 : ℝ) * u)) μ)
    (hν_minus : Integrable (fun u => Real.exp ((1 - 2 * A) * u)) ν)
    (hν_plus : Integrable (fun u => Real.exp ((-1 : ℝ) * u)) ν)
    (hM_bound : ∀ σ ∈ Icc (1 - 2 * A) (-1),
      laplaceTransformReal μ σ + laplaceTransformReal ν σ ≤ M)
    (hδ_bound : ∀ σ ∈ Icc (1 - 2 * A) (-1),
      |laplaceTransformReal μ σ - laplaceTransformReal ν σ| ≤ δ)
    (N : ℕ) {φ : ℝ → ℝ} (hφ_diff : Differentiable ℝ φ)
    (hφ'_diff : Differentiable ℝ (deriv φ))
    (hsupp : ∀ u : ℝ, (N : ℝ) < |u| → φ u = 0)
    {M_φ : ℝ} (hM_φ : 0 ≤ M_φ)
    (hφ0 : ∀ u, |φ u| ≤ M_φ) (hφ1 : ∀ u, |deriv φ u| ≤ M_φ)
    (hφ2 : ∀ u, |deriv (deriv φ) u| ≤ M_φ) :
    |(∫ u : ℝ, φ u ∂μ) - (∫ u : ℝ, φ u ∂ν)| ≤
      hermiteConstant N * (A + 1) ^ 2 * Real.exp (A * (N : ℝ)) *
        (M ^ (1 - midpointHarmonicExp A (2 * π)) *
          δ ^ (midpointHarmonicExp A (2 * π))) * M_φ := by
  let E : ℂ → ℂ := fun z => laplaceTransform μ z - laplaceTransform ν z
  have hE_diff : DifferentiableOn ℂ E {s : ℂ | s.re ∈ Ioo (1 - 2 * A) (-1)} :=
    (differentiableOn_laplaceTransform hμ_minus hμ_plus).sub
      (differentiableOn_laplaceTransform hν_minus hν_plus)
  have hE_cont : ContinuousOn E {s : ℂ | s.re ∈ Icc (1 - 2 * A) (-1)} :=
    (continuousOn_laplaceTransform hμ_minus hμ_plus).sub
      (continuousOn_laplaceTransform hν_minus hν_plus)
  have hE_M :
      ∀ σ ∈ Icc (1 - 2 * A) (-1), ∀ t : ℝ, ‖E ((σ : ℂ) + (t : ℂ) * I)‖ ≤ M := by
    intro σ hσ t
    dsimp [E]
    calc ‖laplaceTransform μ ((σ : ℂ) + (t : ℂ) * I) -
          laplaceTransform ν ((σ : ℂ) + (t : ℂ) * I)‖
        ≤ ‖laplaceTransform μ ((σ : ℂ) + (t : ℂ) * I)‖ +
          ‖laplaceTransform ν ((σ : ℂ) + (t : ℂ) * I)‖ := norm_sub_le _ _
      _ ≤ laplaceTransformReal μ σ + laplaceTransformReal ν σ :=
          add_le_add (norm_laplaceTransform_le_laplaceTransformReal μ σ t)
            (norm_laplaceTransform_le_laplaceTransformReal ν σ t)
      _ ≤ M := hM_bound σ hσ
  have hE_δ : ∀ σ ∈ Icc (1 - 2 * A) (-1), ‖E (σ : ℂ)‖ ≤ δ := by
    intro σ hσ
    dsimp [E]
    rw [laplaceTransform_ofReal, laplaceTransform_ofReal, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    exact hδ_bound σ hσ
  have h_mid_mem : -A ∈ Icc (1 - 2 * A) (-1) := ⟨by linarith, by linarith⟩
  have : IsFiniteMeasure (tiltedMeasure A μ) :=
    isFiniteMeasure_tiltedMeasure (integrable_exp_mul_of_mem_Icc hμ_minus hμ_plus h_mid_mem)
  have : IsFiniteMeasure (tiltedMeasure A ν) :=
    isFiniteMeasure_tiltedMeasure (integrable_exp_mul_of_mem_Icc hν_minus hν_plus h_mid_mem)
  have hν_A : tiltedMeasure A ν (univ \ range (Int.cast : ℤ → ℝ)) = 0 :=
    tiltedMeasure_compl_intCast_eq_zero A hν
  let ε : ℝ := M ^ (1 - midpointHarmonicExp A (2 * π)) * δ ^ (midpointHarmonicExp A (2 * π))
  have hε_nonneg : 0 ≤ ε := by
    dsimp [ε]
    have hM_pos : 0 < M := lt_of_lt_of_le hδ hδM
    positivity
  have h_four : ∀ t ∈ Icc (0 : ℝ) (2 * π),
      ‖(∫ u : ℝ, Complex.exp (I * (t : ℂ) * (u : ℂ)) ∂(tiltedMeasure A μ)) -
        (∫ u : ℝ, Complex.exp (I * (t : ℂ) * (u : ℂ)) ∂(tiltedMeasure A ν))‖ ≤
        ε := by
    intro t ht
    rw [fourier_tiltedMeasure_eq_laplaceTransform, fourier_tiltedMeasure_eq_laplaceTransform]
    exact norm_le_midpoint_two_constants hA (by positivity : 0 < 2 * π) hδ hδM
      hE_diff hE_cont hE_M hE_δ ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  have hA_nonneg : 0 ≤ A := by linarith
  let M_ψ : ℝ := (A + 1) ^ 2 * Real.exp (A * (N : ℝ)) * M_φ
  have hM_ψ_nonneg : 0 ≤ M_ψ := by positivity
  have h_est := abs_integral_sub_le_of_fourier_bound hν_A N
    (differentiable_tiltedTest A hφ_diff)
    (differentiable_deriv_tiltedTest A hφ_diff hφ'_diff)
    (fun u hu => tiltedTest_eq_zero_of_support A hsupp hu)
    hM_ψ_nonneg hε_nonneg
    (abs_tiltedTest_le_sq hA_nonneg hM_φ hsupp hφ0)
    (abs_deriv_tiltedTest_le_sq hA_nonneg hφ_diff hM_φ hsupp hφ0 hφ1)
    (abs_deriv2_tiltedTest_le_sq hA_nonneg hφ_diff hφ'_diff hM_φ hsupp hφ0 hφ1 hφ2)
    h_four
  rw [integral_tiltedTest_tiltedMeasure, integral_tiltedTest_tiltedMeasure] at h_est
  calc |(∫ u : ℝ, φ u ∂μ) - (∫ u : ℝ, φ u ∂ν)|
      ≤ hermiteConstant N * ε * M_ψ := h_est
    _ = hermiteConstant N * (A + 1) ^ 2 * Real.exp (A * (N : ℝ)) *
          (M ^ (1 - midpointHarmonicExp A (2 * π)) *
            δ ^ (midpointHarmonicExp A (2 * π))) * M_φ := by
        dsimp [ε, M_ψ]
        ring

/-- Version of `abs_integral_sub_le_of_laplaceReal_bound` assuming `ContDiff ℝ 2 φ`. -/
theorem abs_integral_sub_le_of_laplaceReal_bound_contDiff {A M δ : ℝ}
    (hA : 1 < A) (hδ : 0 < δ) (hδM : δ ≤ M)
    {μ ν : Measure ℝ} (hν : ν (univ \ range (Int.cast : ℤ → ℝ)) = 0)
    (hμ_minus : Integrable (fun u => Real.exp ((1 - 2 * A) * u)) μ)
    (hμ_plus : Integrable (fun u => Real.exp ((-1 : ℝ) * u)) μ)
    (hν_minus : Integrable (fun u => Real.exp ((1 - 2 * A) * u)) ν)
    (hν_plus : Integrable (fun u => Real.exp ((-1 : ℝ) * u)) ν)
    (hM_bound : ∀ σ ∈ Icc (1 - 2 * A) (-1),
      laplaceTransformReal μ σ + laplaceTransformReal ν σ ≤ M)
    (hδ_bound : ∀ σ ∈ Icc (1 - 2 * A) (-1),
      |laplaceTransformReal μ σ - laplaceTransformReal ν σ| ≤ δ)
    (N : ℕ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, (N : ℝ) < |u| → φ u = 0)
    {M_φ : ℝ} (hM_φ : 0 ≤ M_φ)
    (hφ0 : ∀ u, |φ u| ≤ M_φ) (hφ1 : ∀ u, |deriv φ u| ≤ M_φ)
    (hφ2 : ∀ u, |deriv (deriv φ) u| ≤ M_φ) :
    |(∫ u : ℝ, φ u ∂μ) - (∫ u : ℝ, φ u ∂ν)| ≤
      hermiteConstant N * (A + 1) ^ 2 * Real.exp (A * (N : ℝ)) *
        (M ^ (1 - midpointHarmonicExp A (2 * π)) *
          δ ^ (midpointHarmonicExp A (2 * π))) * M_φ := by
  have hφ_diff : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hφ_succ : ContDiff ℝ (1 + 1) φ := hφ
  have hφ'_diff : Differentiable ℝ (deriv φ) :=
    ((contDiff_succ_iff_deriv.mp hφ_succ).2.2).differentiable (by norm_num)
  exact abs_integral_sub_le_of_laplaceReal_bound hA hδ hδM hν
    hμ_minus hμ_plus hν_minus hν_plus hM_bound hδ_bound
    N hφ_diff hφ'_diff hsupp hM_φ hφ0 hφ1 hφ2

/-- For any `0 < γ < α`, there exists `A > 1` large enough that
`γ ≤ α * midpointHarmonicExp A (2 * π)`. -/
lemma exists_gt_one_le_mul_midpointHarmonicExp {α γ : ℝ} (hα : 0 < α) (hγα : γ < α) :
    ∃ A : ℝ, 1 < A ∧ γ ≤ α * midpointHarmonicExp A (2 * π) := by
  have h_lim := tendsto_midpointHarmonicExp_atTop (by positivity : 0 < 2 * π)
  have h_lt : γ / α < 1 := (div_lt_one hα).mpr hγα
  have h_ev1 : ∀ᶠ A : ℝ in atTop, γ / α < midpointHarmonicExp A (2 * π) :=
    h_lim.eventually (eventually_gt_nhds h_lt)
  have h_ev : ∀ᶠ A : ℝ in atTop, 1 < A ∧ γ / α < midpointHarmonicExp A (2 * π) :=
    (eventually_gt_atTop 1).and h_ev1
  obtain ⟨A, hA1, hA2⟩ := h_ev.exists
  refine ⟨A, hA1, ?_⟩
  linarith [(div_lt_iff₀ hα).mp hA2]

/-- **Asymptotic Power-Law Laplace-to-`C_c^2` Tauberian Theorem on `ℤ`**:
Given `0 < γ < α`, `0 < C_0`, `0 < M`, and `N : ℕ`, there exist a strip parameter `A > 1` and a
constant `C > 0` such that for any `J ≥ 1`, any measures `μ, ν` on `ℝ` with `ν` supported on
`ℤ` satisfying the Laplace bounds on `[1 - 2A, -1]` with `δ = C_0 * J ^ (-α)`, and any twice
differentiable test function `φ` supported in `[-N, N]` with `|φ|, |φ'|, |φ''| ≤ M_φ`,
`|(∫ φ dμ) - (∫ φ dν)| ≤ C * J ^ (-γ) * M_φ`. -/
theorem exists_const_abs_integral_sub_le_rpow {α γ C_0 M : ℝ}
    (hγ : 0 < γ) (hγα : γ < α) (hC_0 : 0 < C_0) (hM : 0 < M) (N : ℕ) :
    ∃ A > 1, ∃ C > 0, ∀ {J : ℝ}, 1 ≤ J →
      ∀ {μ ν : Measure ℝ}, ν (univ \ range (Int.cast : ℤ → ℝ)) = 0 →
      Integrable (fun u => Real.exp ((1 - 2 * A) * u)) μ →
      Integrable (fun u => Real.exp ((-1 : ℝ) * u)) μ →
      Integrable (fun u => Real.exp ((1 - 2 * A) * u)) ν →
      Integrable (fun u => Real.exp ((-1 : ℝ) * u)) ν →
      (∀ σ ∈ Icc (1 - 2 * A) (-1),
        laplaceTransformReal μ σ + laplaceTransformReal ν σ ≤ M) →
      (∀ σ ∈ Icc (1 - 2 * A) (-1),
        |laplaceTransformReal μ σ - laplaceTransformReal ν σ| ≤ C_0 * J ^ (-α)) →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      Differentiable ℝ φ → Differentiable ℝ (deriv φ) →
      (∀ u : ℝ, (N : ℝ) < |u| → φ u = 0) →
      0 ≤ M_φ →
      (∀ u, |φ u| ≤ M_φ) → (∀ u, |deriv φ u| ≤ M_φ) →
      (∀ u, |deriv (deriv φ) u| ≤ M_φ) →
      |(∫ u : ℝ, φ u ∂μ) - (∫ u : ℝ, φ u ∂ν)| ≤ C * J ^ (-γ) * M_φ := by
  have hα : 0 < α := lt_trans hγ hγα
  obtain ⟨A, hA, hθ_ge⟩ := exists_gt_one_le_mul_midpointHarmonicExp hα hγα
  let θ := midpointHarmonicExp A (2 * π)
  have hθ_pos : 0 < θ := midpointHarmonicExp_pos hA (by positivity)
  have hθ_lt : θ < 1 := midpointHarmonicExp_lt_one A (2 * π)
  let M' := max M C_0
  have hM'_pos : 0 < M' := lt_of_lt_of_le hM (le_max_left M C_0)
  let C := hermiteConstant N * (A + 1) ^ 2 * Real.exp (A * (N : ℝ)) *
    (M' ^ (1 - θ) * C_0 ^ θ)
  have hC_pos : 0 < C := by
    dsimp [C]
    have hN : 0 < hermiteConstant N := hermiteConstant_pos N
    positivity
  refine ⟨A, hA, C, hC_pos, ?_⟩
  intro J hJ μ ν hν hμ_m hμ_p hν_m hν_p hM_bd hδ_bd φ M_φ hφ hφ' hsupp hM_φ hφ0 hφ1
    hφ2
  have hJ_pos : 0 < J := lt_of_lt_of_le zero_lt_one hJ
  let δ := C_0 * J ^ (-α)
  have hδ_pos : 0 < δ := by positivity
  have hJ_rpow_le_one : J ^ (-α) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hJ (by linarith)
  have hδ_le_M' : δ ≤ M' := by
    calc C_0 * J ^ (-α) ≤ C_0 * 1 := mul_le_mul_of_nonneg_left hJ_rpow_le_one hC_0.le
      _ = C_0 := mul_one C_0
      _ ≤ M' := le_max_right M C_0
  have hM'_bd : ∀ σ ∈ Icc (1 - 2 * A) (-1),
      laplaceTransformReal μ σ + laplaceTransformReal ν σ ≤ M' :=
    fun σ hσ => (hM_bd σ hσ).trans (le_max_left M C_0)
  have h_base := abs_integral_sub_le_of_laplaceReal_bound hA hδ_pos hδ_le_M' hν
    hμ_m hμ_p hν_m hν_p hM'_bd hδ_bd N hφ hφ' hsupp hM_φ hφ0 hφ1 hφ2
  have hδ_rpow : δ ^ θ ≤ C_0 ^ θ * J ^ (-γ) := by
    dsimp [δ]
    rw [Real.mul_rpow hC_0.le (Real.rpow_nonneg hJ_pos.le _),
      ← Real.rpow_mul hJ_pos.le]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hC_0.le θ)
    exact Real.rpow_le_rpow_of_exponent_le hJ (by linarith)
  have h_const_nonneg :
      0 ≤ hermiteConstant N * (A + 1) ^ 2 * Real.exp (A * (N : ℝ)) * M' ^ (1 - θ) := by
    have hN : 0 < hermiteConstant N := hermiteConstant_pos N
    positivity
  calc |(∫ u : ℝ, φ u ∂μ) - (∫ u : ℝ, φ u ∂ν)|
      ≤ hermiteConstant N * (A + 1) ^ 2 * Real.exp (A * (N : ℝ)) *
          (M' ^ (1 - θ) * δ ^ θ) * M_φ := h_base
    _ = (hermiteConstant N * (A + 1) ^ 2 * Real.exp (A * (N : ℝ)) * M' ^ (1 - θ)) *
          δ ^ θ * M_φ := by ring
    _ ≤ (hermiteConstant N * (A + 1) ^ 2 * Real.exp (A * (N : ℝ)) * M' ^ (1 - θ)) *
          (C_0 ^ θ * J ^ (-γ)) * M_φ := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hδ_rpow h_const_nonneg) hM_φ
    _ = C * J ^ (-γ) * M_φ := by
        dsimp [C]
        ring

end CFT.LightconeBootstrap
