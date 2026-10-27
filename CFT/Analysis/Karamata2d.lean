/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Balt van Rees
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Quantitative Two-Variable Fourier-Laplace Tauberian Theorem on `(0, ∞)²`

This file establishes the non-asymptotic and quantitative `O(Δ^{-γ})` two-variable Fourier-Laplace
Tauberian theorems for measures on `ℝ × ℝ`.

## Main Definitions & Results

1. **Two-Variable Laplace Transforms & Exponential Tilting**:
   - `laplaceTransform2d μ zl zr`: two-variable complex Laplace transform
     `∫ p, exp(zl * p.1 + zr * p.2) ∂μ`.
   - `laplaceTransformReal2d μ σl σr`: two-variable real Laplace transform
     `∫ p, exp(σl * p.1 + σr * p.2) ∂μ`.
   - `tiltedMeasure2d A μ` and `tiltedTest2d A ψ`: exponential tilting by `exp(∓A(p.1 + p.2))`.
   - `fourier_tiltedMeasure2d_eq_laplaceTransform2d`: the 2D Fourier transform of
     `tiltedMeasure2d A μ` at `(tl, tr)` equals `laplaceTransform2d μ (-A + i tl) (-A + i tr)`.

2. **Bandlimited Fourier Truncation & Tail Decay**:
   - `HasFourierDecay2d φ g C_g`: Fourier inversion representation of `φ : ℝ × ℝ → ℝ` with
     `‖g q‖ ≤ C_g * (1 + q.1^2)⁻¹ * (1 + q.2^2)⁻¹`.
   - `freqBox R` and `bandlimitedApprox2d g R`: frequency truncation to `[-R, R] × [-R, R]`.
   - `norm_sub_bandlimitedApprox2d_le`: uniform `L^∞` tail bound `(4 * π * C_g) / R`.
   - `integral_bandlimitedApprox2d_tiltedMeasure2d`: Fubini pairing identity relating the integral
     of `bandlimitedApprox2d g R` against `tiltedMeasure2d A μ` to the integral of
     `g q * laplaceTransform2d μ (-A + i q.1) (-A + i q.2)` over `freqBox R`.

3. **Non-Asymptotic & Quantitative `O(Δ^{-γ})` 2D Tauberian Theorems**:
   - `abs_integral_sub_le_of_laplace2d_bound`: non-asymptotic bound
     `|(∫ ψ dμ) - (∫ ψ dν)| ≤ π^2 * C_g * ε + (4 * π * C_g * M) / R`.
   - `exists_const_abs_integral_sub_le_rpow_2d`: quantitative `O(Δ^{-γ})` Tauberian theorem with
     optimal frequency cutoff `R = Δ^γ` and `γ = α / (p_deg + 1)`.
-/

open MeasureTheory Set Filter Metric Real Complex Topology
open scoped ENNReal

namespace CFT.ConeTauberian

/-! ## Section 1: Two-Variable Complex & Real Laplace Transforms and Tilted Measures -/

/-- The two-variable complex Laplace transform `∫ p, exp(zl * p.1 + zr * p.2) dμ(p)` of a
measure `μ` on `ℝ × ℝ`. -/
noncomputable def laplaceTransform2d (μ : Measure (ℝ × ℝ)) (zl zr : ℂ) : ℂ :=
  ∫ p : ℝ × ℝ, Complex.exp (zl * (p.1 : ℂ) + zr * (p.2 : ℂ)) ∂μ

/-- The two-variable real Laplace transform `∫ p, exp(σl * p.1 + σr * p.2) dμ(p)` of a
measure `μ` on `ℝ × ℝ`. -/
noncomputable def laplaceTransformReal2d (μ : Measure (ℝ × ℝ)) (σl σr : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, Real.exp (σl * p.1 + σr * p.2) ∂μ

lemma norm_exp_add_mul_ofReal (zl zr : ℂ) (p : ℝ × ℝ) :
    ‖Complex.exp (zl * (p.1 : ℂ) + zr * (p.2 : ℂ))‖ =
      Real.exp (zl.re * p.1 + zr.re * p.2) := by
  rw [Complex.norm_exp]
  simp [add_re, mul_re]

lemma norm_laplaceTransform2d_le_laplaceTransformReal2d
    (μ : Measure (ℝ × ℝ)) (σl σr tl tr : ℝ) :
    ‖laplaceTransform2d μ ((σl : ℂ) + (tl : ℂ) * I) ((σr : ℂ) + (tr : ℂ) * I)‖ ≤
      laplaceTransformReal2d μ σl σr := by
  unfold laplaceTransform2d laplaceTransformReal2d
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  dsimp
  rw [norm_exp_add_mul_ofReal]
  simp

/-- The exponentially tilted measure `dμ_A(p) = exp(-A * (p.1 + p.2)) dμ(p)` on `ℝ × ℝ`. -/
noncomputable def tiltedMeasure2d (A : ℝ) (μ : Measure (ℝ × ℝ)) : Measure (ℝ × ℝ) :=
  μ.withDensity (fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-A * (p.1 + p.2))))

/-- The exponentially tilted test function `exp(A * (p.1 + p.2)) * ψ p` on `ℝ × ℝ`. -/
noncomputable def tiltedTest2d (A : ℝ) (ψ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (A * (p.1 + p.2)) * ψ p

lemma continuous_exp_neg_mul_add (A : ℝ) :
    Continuous (fun p : ℝ × ℝ => Real.exp (-A * (p.1 + p.2))) :=
  Real.continuous_exp.comp (continuous_const.mul (continuous_fst.add continuous_snd))

lemma isFiniteMeasure_tiltedMeasure2d {A : ℝ} {μ : Measure (ℝ × ℝ)}
    (h_int : Integrable (fun p : ℝ × ℝ => Real.exp (-A * (p.1 + p.2))) μ) :
    IsFiniteMeasure (tiltedMeasure2d A μ) :=
  isFiniteMeasure_withDensity_ofReal h_int.2

lemma tiltedMeasure2d_univ_eq (A : ℝ) (μ : Measure (ℝ × ℝ)) :
    (tiltedMeasure2d A μ).real univ = laplaceTransformReal2d μ (-A) (-A) := by
  unfold tiltedMeasure2d laplaceTransformReal2d Measure.real
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have h_eq : (fun p : ℝ × ℝ => Real.exp (-A * p.1 + -A * p.2)) =
      fun p : ℝ × ℝ => Real.exp (-A * (p.1 + p.2)) := by
    ext p; ring_nf
  rw [h_eq, integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun p => (Real.exp_pos _).le)
    (continuous_exp_neg_mul_add A).aestronglyMeasurable]

lemma tiltedMeasure2d_univ_le (A : ℝ) (μ : Measure (ℝ × ℝ)) :
    (tiltedMeasure2d A μ).real univ ≤ laplaceTransformReal2d μ (-A) (-A) :=
  (tiltedMeasure2d_univ_eq A μ).le

lemma integral_tiltedMeasure2d_eq_integral_mul (A : ℝ) (μ : Measure (ℝ × ℝ))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ × ℝ → E) :
    ∫ p : ℝ × ℝ, g p ∂(tiltedMeasure2d A μ) =
      ∫ p : ℝ × ℝ, Real.exp (-A * (p.1 + p.2)) • g p ∂μ := by
  let f : ℝ × ℝ → NNReal := fun p => Real.toNNReal (Real.exp (-A * (p.1 + p.2)))
  have hf_meas : Measurable f := (continuous_exp_neg_mul_add A).measurable.real_toNNReal
  change (∫ p : ℝ × ℝ, g p ∂μ.withDensity (fun p => (f p : ℝ≥0∞))) =
    ∫ p : ℝ × ℝ, Real.exp (-A * (p.1 + p.2)) • g p ∂μ
  rw [integral_withDensity_eq_integral_smul hf_meas]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  dsimp [f]
  rw [NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_pos _).le]

lemma integral_tiltedTest2d_tiltedMeasure2d (A : ℝ) (μ : Measure (ℝ × ℝ)) (ψ : ℝ × ℝ → ℝ) :
    ∫ p : ℝ × ℝ, tiltedTest2d A ψ p ∂(tiltedMeasure2d A μ) = ∫ p : ℝ × ℝ, ψ p ∂μ := by
  rw [integral_tiltedMeasure2d_eq_integral_mul]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  dsimp [tiltedTest2d]
  rw [← mul_assoc, ← Real.exp_add]
  have h_zero : -A * (p.1 + p.2) + A * (p.1 + p.2) = 0 := by ring
  rw [h_zero, Real.exp_zero, one_mul]

lemma fourier_tiltedMeasure2d_eq_laplaceTransform2d
    (A : ℝ) (μ : Measure (ℝ × ℝ)) (tl tr : ℝ) :
    ∫ p : ℝ × ℝ,
        Complex.exp (I * ((tl : ℂ) * (p.1 : ℂ) + (tr : ℂ) * (p.2 : ℂ))) ∂(tiltedMeasure2d A μ) =
      laplaceTransform2d μ ((-A : ℂ) + (tl : ℂ) * I) ((-A : ℂ) + (tr : ℂ) * I) := by
  rw [integral_tiltedMeasure2d_eq_integral_mul]
  unfold laplaceTransform2d
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  dsimp
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ## Section 2: Bandlimited Fourier Truncation & Tail Decay on `[-R, R]²` -/

/-- A function `φ : ℝ × ℝ → ℝ` has a 2D Fourier inversion representation with integrable quadratic
decay if `φ(p) = ∫ q, g(q) exp(i (q.1 p.1 + q.2 p.2))` with
`‖g(q)‖ ≤ C_g (1 + q.1^2)⁻¹ (1 + q.2^2)⁻¹`. -/
structure HasFourierDecay2d (φ : ℝ × ℝ → ℝ) (g : ℝ × ℝ → ℂ) (C_g : ℝ) : Prop where
  C_g_nonneg : 0 ≤ C_g
  g_measurable : AEStronglyMeasurable g volume
  norm_g_le : ∀ q : ℝ × ℝ, ‖g q‖ ≤ C_g * ((1 + q.1 ^ 2)⁻¹ * (1 + q.2 ^ 2)⁻¹)
  fourier_eq : ∀ p : ℝ × ℝ,
    (φ p : ℂ) =
      ∫ q : ℝ × ℝ, g q * Complex.exp (I * ((q.1 : ℂ) * (p.1 : ℂ) + (q.2 : ℂ) * (p.2 : ℂ)))

/-- The truncated 2D frequency box `[-R, R] × [-R, R]`. -/
def freqBox (R : ℝ) : Set (ℝ × ℝ) :=
  Icc (-R) R ×ˢ Icc (-R) R

lemma measurableSet_freqBox (R : ℝ) : MeasurableSet (freqBox R) :=
  measurableSet_Icc.prod measurableSet_Icc

/-- The bandlimited approximation to `φ` obtained by restricting the Fourier integral to
`freqBox R`. -/
noncomputable def bandlimitedApprox2d (g : ℝ × ℝ → ℂ) (R : ℝ) (p : ℝ × ℝ) : ℂ :=
  ∫ q in freqBox R, g q * Complex.exp (I * ((q.1 : ℂ) * (p.1 : ℂ) + (q.2 : ℂ) * (p.2 : ℂ)))

lemma norm_exp_I_mul_add_ofReal (q p : ℝ × ℝ) :
    ‖Complex.exp (I * ((q.1 : ℂ) * (p.1 : ℂ) + (q.2 : ℂ) * (p.2 : ℂ)))‖ = 1 := by
  have h_eq : I * ((q.1 : ℂ) * (p.1 : ℂ) + (q.2 : ℂ) * (p.2 : ℂ)) =
      (((q.1 * p.1 + q.2 * p.2 : ℝ) : ℂ) * I) := by
    push_cast
    ring
  rw [h_eq, Complex.norm_exp_ofReal_mul_I]

lemma integrable_inv_one_add_sq_prod :
    Integrable (fun q : ℝ × ℝ => (1 + q.1 ^ 2)⁻¹ * (1 + q.2 ^ 2)⁻¹) volume := by
  rw [Measure.volume_eq_prod]
  exact integrable_inv_one_add_sq.mul_prod integrable_inv_one_add_sq

lemma integral_univ_inv_one_add_sq_prod :
    (∫ q : ℝ × ℝ, (1 + q.1 ^ 2)⁻¹ * (1 + q.2 ^ 2)⁻¹) = π ^ 2 := by
  rw [Measure.volume_eq_prod,
    integral_prod_mul (fun x : ℝ => (1 + x ^ 2)⁻¹) (fun y : ℝ => (1 + y ^ 2)⁻¹),
    integral_univ_inv_one_add_sq]
  ring

lemma integral_Icc_inv_one_add_sq {R : ℝ} (hR : 0 ≤ R) :
    (∫ t in Icc (-R) R, (1 + t ^ 2)⁻¹) = 2 * Real.arctan R := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    integral_inv_one_add_sq, Real.arctan_neg]
  ring

lemma integral_freqBox_inv_one_add_sq_prod {R : ℝ} (hR : 0 ≤ R) :
    (∫ q in freqBox R, (1 + q.1 ^ 2)⁻¹ * (1 + q.2 ^ 2)⁻¹) = (2 * Real.arctan R) ^ 2 := by
  rw [freqBox, Measure.volume_eq_prod,
    setIntegral_prod_mul (fun x : ℝ => (1 + x ^ 2)⁻¹) (fun y : ℝ => (1 + y ^ 2)⁻¹),
    integral_Icc_inv_one_add_sq hR]
  ring

lemma integral_freqBox_inv_one_add_sq_prod_le (R : ℝ) :
    (∫ q in freqBox R, (1 + q.1 ^ 2)⁻¹ * (1 + q.2 ^ 2)⁻¹) ≤ π ^ 2 := by
  rw [ ← integral_univ_inv_one_add_sq_prod]
  exact setIntegral_le_integral integrable_inv_one_add_sq_prod
    (ae_of_all _ fun q => by positivity)

lemma arctan_le_self_of_nonneg {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  have h_int : ∫ t in (0 : ℝ)..x, (1 + t ^ 2)⁻¹ ≤ ∫ _t in (0 : ℝ)..x, (1 : ℝ) :=
    intervalIntegral.integral_mono_on hx
      integrable_inv_one_add_sq.intervalIntegrable
      intervalIntegrable_const
      (fun t _ => inv_le_one_of_one_le₀ (by linarith [sq_nonneg t]))
  simpa [integral_inv_one_add_sq] using h_int

lemma pi_sub_two_mul_arctan_le {R : ℝ} (hR : 0 < R) :
    π - 2 * Real.arctan R ≤ 2 / R := by
  have h_inv : Real.arctan R⁻¹ = π / 2 - Real.arctan R := Real.arctan_inv_of_pos hR
  have h_le : Real.arctan R⁻¹ ≤ R⁻¹ := arctan_le_self_of_nonneg (inv_nonneg.mpr hR.le)
  rw [div_eq_mul_inv]
  linarith

lemma integral_compl_freqBox_inv_one_add_sq_prod_le {R : ℝ} (hR : 0 < R) :
    (∫ q in (freqBox R)ᶜ, (1 + q.1 ^ 2)⁻¹ * (1 + q.2 ^ 2)⁻¹) ≤ 4 * π / R := by
  have h_split := integral_add_compl (measurableSet_freqBox R) integrable_inv_one_add_sq_prod
  rw [integral_freqBox_inv_one_add_sq_prod hR.le, integral_univ_inv_one_add_sq_prod] at h_split
  have h_compl : (∫ q in (freqBox R)ᶜ, (1 + q.1 ^ 2)⁻¹ * (1 + q.2 ^ 2)⁻¹) =
      (π + 2 * Real.arctan R) * (π - 2 * Real.arctan R) := by
    linarith [show (2 * Real.arctan R) ^ 2 +
        (π + 2 * Real.arctan R) * (π - 2 * Real.arctan R) = π ^ 2 by ring]
  rw [h_compl]
  have h_lt : Real.arctan R < π / 2 := Real.arctan_lt_pi_div_two R
  have h_sum_le : π + 2 * Real.arctan R ≤ 2 * π := by linarith
  have h_diff_nonneg : 0 ≤ π - 2 * Real.arctan R := by linarith
  have h_diff_le : π - 2 * Real.arctan R ≤ 2 / R := pi_sub_two_mul_arctan_le hR
  calc (π + 2 * Real.arctan R) * (π - 2 * Real.arctan R)
      ≤ (2 * π) * (2 / R) :=
        mul_le_mul h_sum_le h_diff_le h_diff_nonneg (by positivity)
    _ = 4 * π / R := by ring

lemma HasFourierDecay2d.integrable_g_mul_exp {φ : ℝ × ℝ → ℝ} {g : ℝ × ℝ → ℂ} {C_g : ℝ}
    (h : HasFourierDecay2d φ g C_g) (p : ℝ × ℝ) :
    Integrable
      (fun q : ℝ × ℝ => g q * Complex.exp (I * ((q.1 : ℂ) * (p.1 : ℂ) + (q.2 : ℂ) * (p.2 : ℂ))))
      volume := by
  have h_cont : Continuous
      (fun q : ℝ × ℝ => Complex.exp (I * ((q.1 : ℂ) * (p.1 : ℂ) + (q.2 : ℂ) * (p.2 : ℂ)))) := by
    fun_prop
  refine (integrable_inv_one_add_sq_prod.const_mul C_g).mono'
    (h.g_measurable.mul h_cont.aestronglyMeasurable) (ae_of_all _ fun q => ?_)
  rw [norm_mul, norm_exp_I_mul_add_ofReal, mul_one]
  exact h.norm_g_le q

/-- Uniform pointwise `L^∞` tail bound for the bandlimited Fourier approximation on `freqBox R`. -/
theorem norm_sub_bandlimitedApprox2d_le {φ : ℝ × ℝ → ℝ} {g : ℝ × ℝ → ℂ} {C_g R : ℝ}
    (h : HasFourierDecay2d φ g C_g) (hR : 0 < R) (p : ℝ × ℝ) :
    ‖(φ p : ℂ) - bandlimitedApprox2d g R p‖ ≤ (4 * π * C_g) / R := by
  rw [h.fourier_eq p, bandlimitedApprox2d]
  have h_split := integral_add_compl (measurableSet_freqBox R) (h.integrable_g_mul_exp p)
  have h_sub : (∫ q : ℝ × ℝ,
        g q * Complex.exp (I * ((q.1 : ℂ) * (p.1 : ℂ) + (q.2 : ℂ) * (p.2 : ℂ)))) -
      (∫ q in freqBox R,
        g q * Complex.exp (I * ((q.1 : ℂ) * (p.1 : ℂ) + (q.2 : ℂ) * (p.2 : ℂ)))) =
      ∫ q in (freqBox R)ᶜ,
        g q * Complex.exp (I * ((q.1 : ℂ) * (p.1 : ℂ) + (q.2 : ℂ) * (p.2 : ℂ))) :=
    sub_eq_of_eq_add' h_split.symm
  rw [h_sub]
  have h_bound_int : IntegrableOn
      (fun q : ℝ × ℝ => C_g * ((1 + q.1 ^ 2)⁻¹ * (1 + q.2 ^ 2)⁻¹)) (freqBox R)ᶜ volume :=
    (integrable_inv_one_add_sq_prod.const_mul C_g).integrableOn
  calc ‖∫ q in (freqBox R)ᶜ,
        g q * Complex.exp (I * ((q.1 : ℂ) * (p.1 : ℂ) + (q.2 : ℂ) * (p.2 : ℂ)))‖
      ≤ ∫ q in (freqBox R)ᶜ,
          ‖g q * Complex.exp (I * ((q.1 : ℂ) * (p.1 : ℂ) + (q.2 : ℂ) * (p.2 : ℂ)))‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ q in (freqBox R)ᶜ, C_g * ((1 + q.1 ^ 2)⁻¹ * (1 + q.2 ^ 2)⁻¹) := by
        refine integral_mono_ae (h.integrable_g_mul_exp p).integrableOn.norm h_bound_int
          (ae_of_all _ fun q => ?_)
        dsimp
        rw [norm_mul, norm_exp_I_mul_add_ofReal, mul_one]
        exact h.norm_g_le q
    _ = C_g * ∫ q in (freqBox R)ᶜ, (1 + q.1 ^ 2)⁻¹ * (1 + q.2 ^ 2)⁻¹ :=
        MeasureTheory.integral_const_mul C_g _
    _ ≤ C_g * (4 * π / R) :=
        mul_le_mul_of_nonneg_left (integral_compl_freqBox_inv_one_add_sq_prod_le hR) h.C_g_nonneg
    _ = (4 * π * C_g) / R := by ring

lemma HasFourierDecay2d.abs_le {φ : ℝ × ℝ → ℝ} {g : ℝ × ℝ → ℂ} {C_g : ℝ}
    (h : HasFourierDecay2d φ g C_g) (p : ℝ × ℝ) :
    |φ p| ≤ π ^ 2 * C_g := by
  rw [← Real.norm_eq_abs, ← Complex.norm_real, h.fourier_eq p]
  calc ‖∫ q : ℝ × ℝ, g q * Complex.exp (I * ((q.1 : ℂ) * (p.1 : ℂ) + (q.2 : ℂ) * (p.2 : ℂ)))‖
      ≤ ∫ q : ℝ × ℝ,
          ‖g q * Complex.exp (I * ((q.1 : ℂ) * (p.1 : ℂ) + (q.2 : ℂ) * (p.2 : ℂ)))‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ q : ℝ × ℝ, C_g * ((1 + q.1 ^ 2)⁻¹ * (1 + q.2 ^ 2)⁻¹) := by
        refine integral_mono (h.integrable_g_mul_exp p).norm
          (integrable_inv_one_add_sq_prod.const_mul C_g) (fun q => ?_)
        dsimp
        rw [norm_mul, norm_exp_I_mul_add_ofReal, mul_one]
        exact h.norm_g_le q
    _ = C_g * ∫ q : ℝ × ℝ, (1 + q.1 ^ 2)⁻¹ * (1 + q.2 ^ 2)⁻¹ :=
        MeasureTheory.integral_const_mul C_g _
    _ = π ^ 2 * C_g := by rw [integral_univ_inv_one_add_sq_prod]; ring

lemma HasFourierDecay2d.norm_bandlimitedApprox2d_le {φ : ℝ × ℝ → ℝ} {g : ℝ × ℝ → ℂ} {C_g : ℝ}
    (h : HasFourierDecay2d φ g C_g) (R : ℝ) (p : ℝ × ℝ) :
    ‖bandlimitedApprox2d g R p‖ ≤ π ^ 2 * C_g := by
  unfold bandlimitedApprox2d
  calc ‖∫ q in freqBox R,
        g q * Complex.exp (I * ((q.1 : ℂ) * (p.1 : ℂ) + (q.2 : ℂ) * (p.2 : ℂ)))‖
      ≤ ∫ q in freqBox R,
          ‖g q * Complex.exp (I * ((q.1 : ℂ) * (p.1 : ℂ) + (q.2 : ℂ) * (p.2 : ℂ)))‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ q in freqBox R, C_g * ((1 + q.1 ^ 2)⁻¹ * (1 + q.2 ^ 2)⁻¹) := by
        refine integral_mono (h.integrable_g_mul_exp p).integrableOn.norm
          (integrable_inv_one_add_sq_prod.const_mul C_g).integrableOn (fun q => ?_)
        dsimp
        rw [norm_mul, norm_exp_I_mul_add_ofReal, mul_one]
        exact h.norm_g_le q
    _ = C_g * ∫ q in freqBox R, (1 + q.1 ^ 2)⁻¹ * (1 + q.2 ^ 2)⁻¹ :=
        MeasureTheory.integral_const_mul C_g _
    _ ≤ C_g * π ^ 2 :=
        mul_le_mul_of_nonneg_left (integral_freqBox_inv_one_add_sq_prod_le R) h.C_g_nonneg
    _ = π ^ 2 * C_g := by ring

lemma HasFourierDecay2d.continuous_ofReal {φ : ℝ × ℝ → ℝ} {g : ℝ × ℝ → ℂ} {C_g : ℝ}
    (h : HasFourierDecay2d φ g C_g) : Continuous (fun p : ℝ × ℝ => (φ p : ℂ)) := by
  have h_eq : (fun p : ℝ × ℝ => (φ p : ℂ)) =
      fun p => ∫ q : ℝ × ℝ,
        g q * Complex.exp (I * ((q.1 : ℂ) * (p.1 : ℂ) + (q.2 : ℂ) * (p.2 : ℂ))) :=
    funext h.fourier_eq
  rw [h_eq]
  refine continuous_of_dominated
    (bound := fun q : ℝ × ℝ => C_g * ((1 + q.1 ^ 2)⁻¹ * (1 + q.2 ^ 2)⁻¹))
    (fun p => (h.integrable_g_mul_exp p).1)
    (fun p => ae_of_all _ fun q => by
      rw [norm_mul, norm_exp_I_mul_add_ofReal, mul_one]
      exact h.norm_g_le q)
    (integrable_inv_one_add_sq_prod.const_mul C_g)
    (ae_of_all _ fun q => by fun_prop)

lemma HasFourierDecay2d.continuous_bandlimitedApprox2d {φ : ℝ × ℝ → ℝ} {g : ℝ × ℝ → ℂ} {C_g : ℝ}
    (h : HasFourierDecay2d φ g C_g) (R : ℝ) :
    Continuous (bandlimitedApprox2d g R) := by
  unfold bandlimitedApprox2d
  refine continuous_of_dominated
    (bound := fun q : ℝ × ℝ => C_g * ((1 + q.1 ^ 2)⁻¹ * (1 + q.2 ^ 2)⁻¹))
    (fun p => (h.integrable_g_mul_exp p).integrableOn.1)
    (fun p => ae_of_all _ fun q => by
      rw [norm_mul, norm_exp_I_mul_add_ofReal, mul_one]
      exact h.norm_g_le q)
    (integrable_inv_one_add_sq_prod.const_mul C_g).integrableOn
    (ae_of_all _ fun q => by fun_prop)

/-- Fubini pairing identity: integrating `bandlimitedApprox2d g R` against `tiltedMeasure2d A μ`
swaps the order of integration to an integral over `freqBox R` against `laplaceTransform2d μ`. -/
theorem integral_bandlimitedApprox2d_tiltedMeasure2d
    {φ : ℝ × ℝ → ℝ} {g : ℝ × ℝ → ℂ} {C_g : ℝ} (h : HasFourierDecay2d φ g C_g)
    (A R : ℝ) {μ : Measure (ℝ × ℝ)}
    (hμ : Integrable (fun p : ℝ × ℝ => Real.exp (-A * (p.1 + p.2))) μ) :
    ∫ p : ℝ × ℝ, bandlimitedApprox2d g R p ∂(tiltedMeasure2d A μ) =
      ∫ q in freqBox R,
        g q * laplaceTransform2d μ ((-A : ℂ) + (q.1 : ℂ) * I) ((-A : ℂ) + (q.2 : ℂ) * I) := by
  let μ_A := tiltedMeasure2d A μ
  have : IsFiniteMeasure μ_A := isFiniteMeasure_tiltedMeasure2d hμ
  let ν_R := (volume : Measure (ℝ × ℝ)).restrict (freqBox R)
  let F : (ℝ × ℝ) → (ℝ × ℝ) → ℂ := fun q p =>
    g q * Complex.exp (I * ((q.1 : ℂ) * (p.1 : ℂ) + (q.2 : ℂ) * (p.2 : ℂ)))
  have hF_meas : AEStronglyMeasurable (Function.uncurry F) (ν_R.prod μ_A) := by
    have hg_fst : AEStronglyMeasurable (fun x : (ℝ × ℝ) × (ℝ × ℝ) => g x.1) (ν_R.prod μ_A) :=
      h.g_measurable.restrict.comp_fst
    have hexp_cont : Continuous (fun x : (ℝ × ℝ) × (ℝ × ℝ) =>
        Complex.exp (I * ((x.1.1 : ℂ) * (x.2.1 : ℂ) + (x.1.2 : ℂ) * (x.2.2 : ℂ)))) := by
      fun_prop
    exact hg_fst.mul hexp_cont.aestronglyMeasurable
  have hF_int : Integrable (Function.uncurry F) (ν_R.prod μ_A) := by
    have h_dom : Integrable
        (fun x : (ℝ × ℝ) × (ℝ × ℝ) => C_g * ((1 + x.1.1 ^ 2)⁻¹ * (1 + x.1.2 ^ 2)⁻¹))
        (ν_R.prod μ_A) :=
      ((integrable_inv_one_add_sq_prod.const_mul C_g).integrableOn).comp_fst μ_A
    refine h_dom.mono' hF_meas (ae_of_all _ fun x => ?_)
    change ‖g x.1 * Complex.exp (I * ((x.1.1 : ℂ) * (x.2.1 : ℂ) + (x.1.2 : ℂ) * (x.2.2 : ℂ)))‖ ≤ _
    rw [norm_mul, norm_exp_I_mul_add_ofReal, mul_one]
    exact h.norm_g_le x.1
  change ∫ p : ℝ × ℝ, (∫ q : ℝ × ℝ, F q p ∂ν_R) ∂μ_A = _
  rw [← MeasureTheory.integral_integral_swap hF_int]
  refine integral_congr_ae (ae_of_all _ fun q => ?_)
  dsimp [F, μ_A]
  rw [MeasureTheory.integral_const_mul, fourier_tiltedMeasure2d_eq_laplaceTransform2d]

/-! ## Section 3: Non-Asymptotic & Quantitative `O(Δ^{-γ})` 2D Tauberian Theorems -/

lemma HasFourierDecay2d.integrable_ofReal_tiltedMeasure2d
    {φ : ℝ × ℝ → ℝ} {g : ℝ × ℝ → ℂ} {C_g : ℝ} (h : HasFourierDecay2d φ g C_g)
    (A : ℝ) {μ : Measure (ℝ × ℝ)}
    (hμ : Integrable (fun p : ℝ × ℝ => Real.exp (-A * (p.1 + p.2))) μ) :
    Integrable (fun p : ℝ × ℝ => (φ p : ℂ)) (tiltedMeasure2d A μ) := by
  have : IsFiniteMeasure (tiltedMeasure2d A μ) := isFiniteMeasure_tiltedMeasure2d hμ
  refine Integrable.of_bound h.continuous_ofReal.aestronglyMeasurable (π ^ 2 * C_g)
    (ae_of_all _ fun p => ?_)
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact h.abs_le p

lemma HasFourierDecay2d.integrable_bandlimitedApprox2d_tiltedMeasure2d
    {φ : ℝ × ℝ → ℝ} {g : ℝ × ℝ → ℂ} {C_g : ℝ} (h : HasFourierDecay2d φ g C_g)
    (A R : ℝ) {μ : Measure (ℝ × ℝ)}
    (hμ : Integrable (fun p : ℝ × ℝ => Real.exp (-A * (p.1 + p.2))) μ) :
    Integrable (bandlimitedApprox2d g R) (tiltedMeasure2d A μ) := by
  have : IsFiniteMeasure (tiltedMeasure2d A μ) := isFiniteMeasure_tiltedMeasure2d hμ
  exact Integrable.of_bound (h.continuous_bandlimitedApprox2d R).aestronglyMeasurable
    (π ^ 2 * C_g) (ae_of_all _ (h.norm_bandlimitedApprox2d_le R))

lemma norm_integral_sub_bandlimitedApprox2d_tiltedMeasure2d_le
    {φ : ℝ × ℝ → ℝ} {g : ℝ × ℝ → ℂ} {C_g R : ℝ} (h : HasFourierDecay2d φ g C_g)
    (hR : 0 < R) (A : ℝ) {μ : Measure (ℝ × ℝ)}
    (hμ : Integrable (fun p : ℝ × ℝ => Real.exp (-A * (p.1 + p.2))) μ) :
    ‖∫ p : ℝ × ℝ, ((φ p : ℂ) - bandlimitedApprox2d g R p) ∂(tiltedMeasure2d A μ)‖ ≤
      ((4 * π * C_g) / R) * laplaceTransformReal2d μ (-A) (-A) := by
  have : IsFiniteMeasure (tiltedMeasure2d A μ) := isFiniteMeasure_tiltedMeasure2d hμ
  have h1 := norm_integral_le_of_norm_le_const (μ := tiltedMeasure2d A μ)
    (ae_of_all _ (norm_sub_bandlimitedApprox2d_le h hR))
  have h_nonneg : 0 ≤ (4 * π * C_g) / R := by
    have : 0 ≤ C_g := h.C_g_nonneg
    positivity
  exact h1.trans (mul_le_mul_of_nonneg_left (tiltedMeasure2d_univ_le A μ) h_nonneg)

lemma norm_integral_bandlimitedApprox2d_sub_le
    {φ : ℝ × ℝ → ℝ} {g : ℝ × ℝ → ℂ} {C_g R ε : ℝ} (h : HasFourierDecay2d φ g C_g)
    (hε : 0 ≤ ε) (A : ℝ) {μ ν : Measure (ℝ × ℝ)}
    (hμ : Integrable (fun p : ℝ × ℝ => Real.exp (-A * (p.1 + p.2))) μ)
    (hν : Integrable (fun p : ℝ × ℝ => Real.exp (-A * (p.1 + p.2))) ν)
    (h_diff : ∀ q ∈ freqBox R,
      ‖laplaceTransform2d μ ((-A : ℂ) + (q.1 : ℂ) * I) ((-A : ℂ) + (q.2 : ℂ) * I) -
        laplaceTransform2d ν ((-A : ℂ) + (q.1 : ℂ) * I) ((-A : ℂ) + (q.2 : ℂ) * I)‖ ≤ ε) :
    ‖(∫ p : ℝ × ℝ, bandlimitedApprox2d g R p ∂(tiltedMeasure2d A μ)) -
      (∫ p : ℝ × ℝ, bandlimitedApprox2d g R p ∂(tiltedMeasure2d A ν))‖ ≤
        π ^ 2 * C_g * ε := by
  let L_μ : ℝ × ℝ → ℂ := fun q =>
    laplaceTransform2d μ ((-A : ℂ) + (q.1 : ℂ) * I) ((-A : ℂ) + (q.2 : ℂ) * I)
  let L_ν : ℝ × ℝ → ℂ := fun q =>
    laplaceTransform2d ν ((-A : ℂ) + (q.1 : ℂ) * I) ((-A : ℂ) + (q.2 : ℂ) * I)
  have hL_cont : ∀ {ρ : Measure (ℝ × ℝ)},
      Integrable (fun p : ℝ × ℝ => Real.exp (-A * (p.1 + p.2))) ρ →
      Continuous (fun q : ℝ × ℝ =>
        laplaceTransform2d ρ ((-A : ℂ) + (q.1 : ℂ) * I) ((-A : ℂ) + (q.2 : ℂ) * I)) := by
    intro ρ hρ
    have : IsFiniteMeasure (tiltedMeasure2d A ρ) := isFiniteMeasure_tiltedMeasure2d hρ
    have h_eq : (fun q : ℝ × ℝ =>
        laplaceTransform2d ρ ((-A : ℂ) + (q.1 : ℂ) * I) ((-A : ℂ) + (q.2 : ℂ) * I)) =
        fun q : ℝ × ℝ => ∫ p : ℝ × ℝ,
          Complex.exp (I * ((q.1 : ℂ) * (p.1 : ℂ) + (q.2 : ℂ) * (p.2 : ℂ)))
          ∂(tiltedMeasure2d A ρ) :=
      funext (fun q => (fourier_tiltedMeasure2d_eq_laplaceTransform2d A ρ q.1 q.2).symm)
    rw [h_eq]
    refine continuous_of_dominated (bound := fun _ => (1 : ℝ))
      (fun q => by fun_prop)
      (fun q => ae_of_all _ fun p => (norm_exp_I_mul_add_ofReal q p).le)
      (integrable_const 1)
      (ae_of_all _ fun p => by fun_prop)
  have h_int_μ : IntegrableOn (fun q => g q * L_μ q) (freqBox R) volume := by
    refine ((integrable_inv_one_add_sq_prod.const_mul
      (C_g * laplaceTransformReal2d μ (-A) (-A))).integrableOn).mono'
      (h.g_measurable.restrict.mul (hL_cont hμ).aestronglyMeasurable)
      (ae_of_all _ fun q => ?_)
    dsimp [L_μ]
    rw [norm_mul, mul_right_comm]
    have hL_le : ‖L_μ q‖ ≤ laplaceTransformReal2d μ (-A) (-A) := by
      simpa [L_μ, Complex.ofReal_neg] using
        norm_laplaceTransform2d_le_laplaceTransformReal2d μ (-A) (-A) q.1 q.2
    exact mul_le_mul (h.norm_g_le q) hL_le (norm_nonneg _)
      (mul_nonneg h.C_g_nonneg (by positivity))
  have h_int_ν : IntegrableOn (fun q => g q * L_ν q) (freqBox R) volume := by
    refine ((integrable_inv_one_add_sq_prod.const_mul
      (C_g * laplaceTransformReal2d ν (-A) (-A))).integrableOn).mono'
      (h.g_measurable.restrict.mul (hL_cont hν).aestronglyMeasurable)
      (ae_of_all _ fun q => ?_)
    dsimp [L_ν]
    rw [norm_mul, mul_right_comm]
    have hL_le : ‖L_ν q‖ ≤ laplaceTransformReal2d ν (-A) (-A) := by
      simpa [L_ν, Complex.ofReal_neg] using
        norm_laplaceTransform2d_le_laplaceTransformReal2d ν (-A) (-A) q.1 q.2
    exact mul_le_mul (h.norm_g_le q) hL_le (norm_nonneg _)
      (mul_nonneg h.C_g_nonneg (by positivity))
  rw [integral_bandlimitedApprox2d_tiltedMeasure2d h A R hμ,
    integral_bandlimitedApprox2d_tiltedMeasure2d h A R hν]
  change ‖(∫ q in freqBox R, g q * L_μ q) - (∫ q in freqBox R, g q * L_ν q)‖ ≤ _
  rw [← integral_sub h_int_μ h_int_ν]
  have h_sub_eq : (fun q => g q * L_μ q - g q * L_ν q) = fun q => g q * (L_μ q - L_ν q) := by
    ext q; ring
  rw [h_sub_eq]
  have h_sub_int : IntegrableOn (fun q => g q * (L_μ q - L_ν q)) (freqBox R) volume := by
    rw [← h_sub_eq]
    exact h_int_μ.sub h_int_ν
  have h_dom_int : IntegrableOn
      (fun q : ℝ × ℝ => C_g * ε * ((1 + q.1 ^ 2)⁻¹ * (1 + q.2 ^ 2)⁻¹)) (freqBox R) volume :=
    (integrable_inv_one_add_sq_prod.const_mul (C_g * ε)).integrableOn
  calc ‖∫ q in freqBox R, g q * (L_μ q - L_ν q)‖
      ≤ ∫ q in freqBox R, ‖g q * (L_μ q - L_ν q)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ q in freqBox R, C_g * ε * ((1 + q.1 ^ 2)⁻¹ * (1 + q.2 ^ 2)⁻¹) := by
        refine setIntegral_mono_on h_sub_int.norm h_dom_int (measurableSet_freqBox R)
          (fun q hq => ?_)
        rw [norm_mul, mul_right_comm C_g ε]
        exact mul_le_mul (h.norm_g_le q) (h_diff q hq) (norm_nonneg _)
          (mul_nonneg h.C_g_nonneg (by positivity))
    _ = C_g * ε * ∫ q in freqBox R, (1 + q.1 ^ 2)⁻¹ * (1 + q.2 ^ 2)⁻¹ :=
        MeasureTheory.integral_const_mul (C_g * ε) _
    _ ≤ C_g * ε * π ^ 2 :=
        mul_le_mul_of_nonneg_left (integral_freqBox_inv_one_add_sq_prod_le R)
          (mul_nonneg h.C_g_nonneg hε)
    _ = π ^ 2 * C_g * ε := by ring

/-- **Non-Asymptotic 2D Fourier-Laplace Tauberian Bound**:
Given two measures `μ, ν` on `ℝ × ℝ` whose real Laplace transforms at `(-A, -A)` sum to at most `M`
and whose complex Laplace transforms on `freqBox R` (`R > 0`) agree to within `ε`, any test function
`ψ : ℝ × ℝ → ℝ` whose tilted version `tiltedTest2d A ψ` satisfies `HasFourierDecay2d` with constant
`C_g` obeys `|(∫ ψ dμ) - (∫ ψ dν)| ≤ π^2 * C_g * ε + (4 * π * C_g * M) / R`. -/
theorem abs_integral_sub_le_of_laplace2d_bound
    {A M ε R C_g : ℝ} (hε : 0 ≤ ε) (hR : 0 < R)
    {μ ν : Measure (ℝ × ℝ)}
    (hμ : Integrable (fun p : ℝ × ℝ => Real.exp (-A * (p.1 + p.2))) μ)
    (hν : Integrable (fun p : ℝ × ℝ => Real.exp (-A * (p.1 + p.2))) ν)
    (hM_bound : laplaceTransformReal2d μ (-A) (-A) + laplaceTransformReal2d ν (-A) (-A) ≤ M)
    (h_diff : ∀ q ∈ freqBox R,
      ‖laplaceTransform2d μ ((-A : ℂ) + (q.1 : ℂ) * I) ((-A : ℂ) + (q.2 : ℂ) * I) -
        laplaceTransform2d ν ((-A : ℂ) + (q.1 : ℂ) * I) ((-A : ℂ) + (q.2 : ℂ) * I)‖ ≤ ε)
    {ψ : ℝ × ℝ → ℝ} {g : ℝ × ℝ → ℂ}
    (hψ : HasFourierDecay2d (tiltedTest2d A ψ) g C_g) :
    |(∫ p : ℝ × ℝ, ψ p ∂μ) - (∫ p : ℝ × ℝ, ψ p ∂ν)| ≤
      π ^ 2 * C_g * ε + (4 * π * C_g * M) / R := by
  let φ := tiltedTest2d A ψ
  let B := bandlimitedApprox2d g R
  let μ_A := tiltedMeasure2d A μ
  let ν_A := tiltedMeasure2d A ν
  rw [← integral_tiltedTest2d_tiltedMeasure2d A μ ψ,
    ← integral_tiltedTest2d_tiltedMeasure2d A ν ψ]
  rw [← Real.norm_eq_abs, ← Complex.norm_real, Complex.ofReal_sub,
    ← integral_complex_ofReal, ← integral_complex_ofReal]
  have h_decomp_μ : (∫ p : ℝ × ℝ, (φ p : ℂ) ∂μ_A) =
      (∫ p : ℝ × ℝ, B p ∂μ_A) + ∫ p : ℝ × ℝ, ((φ p : ℂ) - B p) ∂μ_A := by
    have h_add := integral_add (hψ.integrable_bandlimitedApprox2d_tiltedMeasure2d A R hμ)
      ((hψ.integrable_ofReal_tiltedMeasure2d A hμ).sub
        (hψ.integrable_bandlimitedApprox2d_tiltedMeasure2d A R hμ))
    simpa [φ, B, μ_A] using h_add
  have h_decomp_ν : (∫ p : ℝ × ℝ, (φ p : ℂ) ∂ν_A) =
      (∫ p : ℝ × ℝ, B p ∂ν_A) + ∫ p : ℝ × ℝ, ((φ p : ℂ) - B p) ∂ν_A := by
    have h_add := integral_add (hψ.integrable_bandlimitedApprox2d_tiltedMeasure2d A R hν)
      ((hψ.integrable_ofReal_tiltedMeasure2d A hν).sub
        (hψ.integrable_bandlimitedApprox2d_tiltedMeasure2d A R hν))
    simpa [φ, B, ν_A] using h_add
  change ‖(∫ p : ℝ × ℝ, (φ p : ℂ) ∂μ_A) - (∫ p : ℝ × ℝ, (φ p : ℂ) ∂ν_A)‖ ≤ _
  rw [h_decomp_μ, h_decomp_ν]
  have h_rew : ((∫ p, B p ∂μ_A) + ∫ p, ((φ p : ℂ) - B p) ∂μ_A) -
      ((∫ p, B p ∂ν_A) + ∫ p, ((φ p : ℂ) - B p) ∂ν_A) =
      ((∫ p, B p ∂μ_A) - (∫ p, B p ∂ν_A)) +
        ((∫ p, ((φ p : ℂ) - B p) ∂μ_A) - (∫ p, ((φ p : ℂ) - B p) ∂ν_A)) := by ring
  rw [h_rew]
  have h_tri1 := norm_add_le ((∫ p, B p ∂μ_A) - (∫ p, B p ∂ν_A))
    ((∫ p, ((φ p : ℂ) - B p) ∂μ_A) - (∫ p, ((φ p : ℂ) - B p) ∂ν_A))
  have h_tri2 := norm_sub_le (∫ p, ((φ p : ℂ) - B p) ∂μ_A) (∫ p, ((φ p : ℂ) - B p) ∂ν_A)
  have h_band := norm_integral_bandlimitedApprox2d_sub_le hψ hε A hμ hν h_diff
  have h_tail_μ := norm_integral_sub_bandlimitedApprox2d_tiltedMeasure2d_le hψ hR A hμ
  have h_tail_ν := norm_integral_sub_bandlimitedApprox2d_tiltedMeasure2d_le hψ hR A hν
  have h_factor_nonneg : 0 ≤ (4 * π * C_g) / R := by
    have : 0 ≤ C_g := hψ.C_g_nonneg
    positivity
  have h_tail_sum :
      ((4 * π * C_g) / R) * laplaceTransformReal2d μ (-A) (-A) +
        ((4 * π * C_g) / R) * laplaceTransformReal2d ν (-A) (-A) ≤
        (4 * π * C_g * M) / R := by
    calc ((4 * π * C_g) / R) * laplaceTransformReal2d μ (-A) (-A) +
          ((4 * π * C_g) / R) * laplaceTransformReal2d ν (-A) (-A)
        = ((4 * π * C_g) / R) *
            (laplaceTransformReal2d μ (-A) (-A) + laplaceTransformReal2d ν (-A) (-A)) := by ring
      _ ≤ ((4 * π * C_g) / R) * M := mul_le_mul_of_nonneg_left hM_bound h_factor_nonneg
      _ = (4 * π * C_g * M) / R := by ring
  linarith

/-- **Quantitative `O(Δ^{-γ})` Power-Law 2D Tauberian Theorem**:
Given `α > 0`, `p_deg ≥ 0`, `M > 0`, `C_0 > 0`, and `A : ℝ`, set `γ := α / (p_deg + 1) > 0`.
For any test function `ψ : ℝ × ℝ → ℝ` whose tilted version `tiltedTest2d A ψ` satisfies
`HasFourierDecay2d`, there exists `C_ψ > 0` such that for all `Δ ≥ 1` and all measures `μ, ν`
whose complex Laplace transforms on `freqBox (Δ^γ)` agree to within
`C_0 * (Δ^γ)^p_deg * Δ^{-α}`, we have `|(∫ ψ dμ) - (∫ ψ dν)| ≤ C_ψ * Δ^{-γ}`. -/
theorem exists_const_abs_integral_sub_le_rpow_2d
    {α p_deg M C_0 A C_g : ℝ} (hα : 0 < α) (hp : 0 ≤ p_deg) (hM : 0 < M) (hC_0 : 0 < C_0)
    {ψ : ℝ × ℝ → ℝ} {g : ℝ × ℝ → ℂ}
    (hψ : HasFourierDecay2d (tiltedTest2d A ψ) g C_g) :
    let γ := α / (p_deg + 1)
    ∃ C_ψ > 0, ∀ {Δ : ℝ}, 1 ≤ Δ →
      ∀ {μ ν : Measure (ℝ × ℝ)},
      Integrable (fun p : ℝ × ℝ => Real.exp (-A * (p.1 + p.2))) μ →
      Integrable (fun p : ℝ × ℝ => Real.exp (-A * (p.1 + p.2))) ν →
      laplaceTransformReal2d μ (-A) (-A) + laplaceTransformReal2d ν (-A) (-A) ≤ M →
      (∀ q ∈ freqBox (Δ ^ γ),
        ‖laplaceTransform2d μ ((-A : ℂ) + (q.1 : ℂ) * I) ((-A : ℂ) + (q.2 : ℂ) * I) -
          laplaceTransform2d ν ((-A : ℂ) + (q.1 : ℂ) * I) ((-A : ℂ) + (q.2 : ℂ) * I)‖ ≤
          C_0 * (Δ ^ γ) ^ p_deg * Δ ^ (-α)) →
      |(∫ p : ℝ × ℝ, ψ p ∂μ) - (∫ p : ℝ × ℝ, ψ p ∂ν)| ≤ C_ψ * Δ ^ (-γ) := by
  intro γ
  let C_ψ : ℝ := π ^ 2 * C_g * C_0 + 4 * π * C_g * M + 1
  have hC_ψ_pos : 0 < C_ψ := by
    dsimp [C_ψ]
    have : 0 ≤ C_g := hψ.C_g_nonneg
    positivity
  refine ⟨C_ψ, hC_ψ_pos, ?_⟩
  intro Δ hΔ μ ν hμ hν hM_bound h_diff
  have hΔ_pos : 0 < Δ := lt_of_lt_of_le zero_lt_one hΔ
  have hp1_pos : 0 < p_deg + 1 := by linarith
  have hγ_pos : 0 < γ := div_pos hα hp1_pos
  let R := Δ ^ γ
  have hR_pos : 0 < R := Real.rpow_pos_of_pos hΔ_pos γ
  let ε := C_0 * R ^ p_deg * Δ ^ (-α)
  have hε_nonneg : 0 ≤ ε := by
    dsimp [ε]
    positivity
  have h_base := abs_integral_sub_le_of_laplace2d_bound hε_nonneg hR_pos hμ hν hM_bound h_diff hψ
  have h_exp_eq : γ * p_deg + -α = -γ := by
    dsimp [γ]
    have hp1_ne : p_deg + 1 ≠ 0 := hp1_pos.ne'
    field_simp
    ring
  have hε_eq : ε = C_0 * Δ ^ (-γ) := by
    dsimp [ε, R]
    rw [← Real.rpow_mul hΔ_pos.le, mul_assoc, ← Real.rpow_add hΔ_pos, h_exp_eq]
  have hR_inv : (4 * π * C_g * M) / R = (4 * π * C_g * M) * Δ ^ (-γ) := by
    dsimp [R]
    rw [div_eq_mul_inv, ← Real.rpow_neg hΔ_pos.le]
  rw [hε_eq, hR_inv] at h_base
  have h_rpow_nonneg : 0 ≤ Δ ^ (-γ) := (Real.rpow_pos_of_pos hΔ_pos (-γ)).le
  calc |(∫ p : ℝ × ℝ, ψ p ∂μ) - (∫ p : ℝ × ℝ, ψ p ∂ν)|
      ≤ π ^ 2 * C_g * (C_0 * Δ ^ (-γ)) + (4 * π * C_g * M) * Δ ^ (-γ) := h_base
    _ = (π ^ 2 * C_g * C_0 + 4 * π * C_g * M) * Δ ^ (-γ) := by ring
    _ ≤ C_ψ * Δ ^ (-γ) := by
        refine mul_le_mul_of_nonneg_right ?_ h_rpow_nonneg
        dsimp [C_ψ]
        linarith

end CFT.ConeTauberian
