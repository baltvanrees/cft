/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Balt van Rees
-/
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import CFT.MonomialBootstrap.MonomialDecomp

/-!
# Spin-$J$ Fourier Projection and the Folded Double Contour Integral

This file formalizes Step 2 of the monomial lightcone bootstrap:

1. **Spin-$J$ Fourier Projection (`fourierProjSpinFull` and `fourierProjSpin`)**:
   Because $\operatorname{UcPdisk} = \{\operatorname{Re}(w_l) < 0, \operatorname{Re}(w_r) < 0\}$ is
   invariant under opposite imaginary shifts $(w_l, w_r) \mapsto (w_l - i\theta, w_r + i\theta)$, we
   project onto the spin-$J$ Laplace transform $L_J(w_l + w_r) = \int e^{h(w_l + w_r)} \, d\mu_J(h)$
   by integrating over $\theta \in [-\pi, \pi]$.
   Using the $\pi$-periodicity of $\mathcal{G}_{\text{mon}}$ (`eval_shift_pi` from
   `MonomialDecomp.lean`), for even spin $J \in 2\mathbb{Z}$ the $\theta$-integral folds onto the
   half-interval $[-\pi/2, \pi/2]$:
   $$L_J(w_l + w_r) = \int_{-\pi/2}^{\pi/2} \frac{d\theta}{\pi} \,
     e^{-J (w_r + i\theta)} \, \mathcal{G}_{\text{mon}}(w_l - i\theta, w_r + i\theta).$$
   On $[-\pi/2, \pi/2]$, the contour stays away from the $u$-channel branch cut at $\theta = \pm\pi$
   and only probes the $t$-channel lightcone limit at $\theta = 0$.

2. **Pairing with a Compactly Supported Smooth Test Function $\varphi(h)$**:
   For a compactly supported smooth test function $\varphi : \mathbb{R} \to \mathbb{R}$, we define
   its Laplace–Fourier transform
   $$\widehat{\varphi}_{\sigma}(t) = \int_{\mathbb{R}} \varphi(h) \, e^{-h (\sigma + i t)} \, dh$$
   and express the pairing $\int_{\mathbb{R}} \varphi(h) \, d\mu_J(h)$ for even $J$ as a folded
   double contour integral over $(t, \theta) \in \mathbb{R} \times [-\pi/2, \pi/2]$ along any
   contour $(\sigma_l + i(t - \theta),\, \sigma_r + i\theta) \in \operatorname{UcPdisk}$ with
   $\sigma_l < 0, \sigma_r < 0$.
-/

open Real Complex Topology Set Metric MeasureTheory Filter
open scoped ComplexConjugate FourierTransform

/-!
## Compactly Supported Smooth Test Functions and Laplace–Fourier Transform
-/

/-- The Laplace–Fourier transform of a test function $\varphi : \mathbb{R} \to \mathbb{R}$ along
the vertical line $\sigma + i t$:
$$\widehat{\varphi}_{\sigma}(t) =
  \int_{\mathbb{R}} \varphi(h) \, e^{-h (\sigma + i t)} \, dh.$$ -/
noncomputable def laplaceFourierTransform (φ : ℝ → ℝ) (σ t : ℝ) : ℂ :=
  ∫ h : ℝ, (φ h : ℂ) * Complex.exp (- (h : ℂ) * ((σ : ℂ) + (t : ℂ) * I))

/-- Uniform $L^1$ bound on `laplaceFourierTransform` for a continuous compactly supported test
function $\varphi$ and $\sigma \in [\sigma_{\min}, \sigma_{\max}]$. -/
lemma exists_bound_laplaceFourierTransform_zero {φ : ℝ → ℝ}
    (hφ_cont : Continuous φ) (hφ_supp : HasCompactSupport φ)
    (σ_min σ_max : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Icc σ_min σ_max, ∀ t : ℝ,
      ‖laplaceFourierTransform φ σ t‖ ≤ C := by
  set M_σ := |σ_min| + |σ_max|
  set B : ℝ → ℝ := fun h => ‖φ h‖ * Real.exp (|h| * M_σ)
  have hB_cont : Continuous B := by fun_prop
  have hB_supp : HasCompactSupport B := hφ_supp.norm.mul_right
  have hB_int : Integrable B := hB_cont.integrable_of_hasCompactSupport hB_supp
  refine ⟨∫ h : ℝ, B h, integral_nonneg (fun h => by positivity), fun σ hσ t => ?_⟩
  unfold laplaceFourierTransform
  refine norm_integral_le_of_norm_le hB_int (Eventually.of_forall (fun h => ?_))
  rw [norm_mul, Complex.norm_real, Complex.norm_exp]
  have h_re : (- (h : ℂ) * ((σ : ℂ) + (t : ℂ) * I)).re = -h * σ := by
    simp [Complex.mul_re]
  rw [h_re]
  have hσ_abs : |σ| ≤ M_σ := by
    dsimp [M_σ]
    exact abs_le.mpr
      ⟨by linarith [hσ.1, neg_abs_le σ_min, abs_nonneg σ_max],
       by linarith [hσ.2, le_abs_self σ_max, abs_nonneg σ_min]⟩
  have h_exp_le : -h * σ ≤ |h| * M_σ := by
    calc
      -h * σ ≤ |-h * σ| := le_abs_self _
      _ = |h| * |σ| := by rw [abs_mul, abs_neg]
      _ ≤ |h| * M_σ := mul_le_mul_of_nonneg_left hσ_abs (abs_nonneg h)
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h_exp_le) (norm_nonneg _)

/-- Integration by parts for `laplaceFourierTransform`: for a compactly supported $C^1$ test
function $\varphi : \mathbb{R} \to \mathbb{R}$,
$$(\sigma + i t) \, \widehat{\varphi}_{\sigma}(t) = \widehat{\varphi'}_{\sigma}(t).$$ -/
lemma mul_laplaceFourierTransform_eq_deriv {φ : ℝ → ℝ}
    (hφ_diff : ContDiff ℝ 1 φ) (hφ_supp : HasCompactSupport φ) (σ t : ℝ) :
    ((σ : ℂ) + (t : ℂ) * I) * laplaceFourierTransform φ σ t =
      laplaceFourierTransform (deriv φ) σ t := by
  have h_deriv_cont : Continuous (deriv φ) := hφ_diff.continuous_deriv le_rfl
  set w : ℂ := (σ : ℂ) + (t : ℂ) * I
  set f : ℝ → ℂ := fun h => (φ h : ℂ) * Complex.exp (- (h : ℂ) * w)
  set g1 : ℝ → ℂ := fun h => ((deriv φ h : ℝ) : ℂ) * Complex.exp (- (h : ℂ) * w)
  set g2 : ℝ → ℂ := fun h => w * f h
  have hg1_cont : Continuous g1 := by
    dsimp [g1]; fun_prop
  have hg1_supp : HasCompactSupport g1 :=
    (hφ_supp.deriv.comp_left Complex.ofReal_zero).mul_right
  have hg1_int : Integrable g1 := hg1_cont.integrable_of_hasCompactSupport hg1_supp
  have hf_cont : Continuous f := by
    have : Continuous φ := hφ_diff.continuous
    dsimp [f]; fun_prop
  have hf_supp : HasCompactSupport f :=
    (hφ_supp.comp_left Complex.ofReal_zero).mul_right
  have hf_int : Integrable f := hf_cont.integrable_of_hasCompactSupport hf_supp
  have hg2_int : Integrable g2 := hf_int.const_mul w
  have h_hasDeriv : ∀ h : ℝ, HasDerivAt f (g1 h - g2 h) h := by
    intro h
    have hd1 : HasDerivAt (fun x : ℝ => (φ x : ℂ)) ((deriv φ h : ℝ) : ℂ) h :=
      ((hφ_diff.differentiable one_ne_zero h).hasDerivAt).ofReal_comp
    have hd2 : HasDerivAt (fun x : ℝ => Complex.exp (- (x : ℂ) * w))
        (-w * Complex.exp (- (h : ℂ) * w)) h := by
      have h_lin : HasDerivAt (fun x : ℝ => - (x : ℂ) * w) (-w) h := by
        simpa using (((hasDerivAt_id h).ofReal_comp).neg).mul_const w
      simpa [mul_comm] using h_lin.cexp
    convert hd1.mul hd2 using 1
    dsimp [g1, g2, f]
    ring
  have h_zero : (∫ h : ℝ, (g1 h - g2 h)) = 0 :=
    integral_eq_zero_of_hasDerivAt_of_integrable h_hasDeriv (hg1_int.sub hg2_int) hf_int
  rw [integral_sub hg1_int hg2_int, sub_eq_zero] at h_zero
  dsimp [laplaceFourierTransform, g1, g2, f, w] at h_zero ⊢
  rw [← integral_const_mul]
  exact h_zero.symm

/-- Rapid decay of `laplaceFourierTransform` at large $|t|$ for a compactly supported $C^k$ test
function $\varphi$, uniformly for $\sigma$ in any compact interval
$[\sigma_{\min}, \sigma_{\max}]$. -/
theorem exists_bound_laplaceFourierTransform {φ : ℝ → ℝ} (k : ℕ)
    (hφ_smooth : ContDiff ℝ k φ) (hφ_supp : HasCompactSupport φ)
    (σ_min σ_max : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Icc σ_min σ_max, ∀ t : ℝ,
      ‖laplaceFourierTransform φ σ t‖ ≤ C / (1 + |t|) ^ k := by
  induction k generalizing φ with
  | zero =>
    rcases exists_bound_laplaceFourierTransform_zero hφ_smooth.continuous hφ_supp σ_min σ_max with
      ⟨C, hC_nonneg, hC⟩
    refine ⟨C, hC_nonneg, fun σ hσ t => ?_⟩
    simpa using hC σ hσ t
  | succ k ih =>
    have hφ_diff1 : ContDiff ℝ 1 φ := hφ_smooth.of_le (by norm_cast; omega)
    have h_deriv_smooth : ContDiff ℝ k (deriv φ) :=
      (by simpa using hφ_smooth : ContDiff ℝ (k + 1) φ).deriv'
    rcases exists_bound_laplaceFourierTransform_zero hφ_smooth.continuous hφ_supp σ_min σ_max with
      ⟨C0, hC0_nonneg, hC0⟩
    rcases ih h_deriv_smooth hφ_supp.deriv with ⟨C1, hC1_nonneg, hC1⟩
    refine ⟨(2 : ℝ) ^ (k + 1) * C0 + 2 * C1, by positivity, fun σ hσ t => ?_⟩
    have h_pos1 : 0 < 1 + |t| := by positivity
    have h_pos_pow : 0 < (1 + |t|) ^ (k + 1) := by positivity
    rw [le_div_iff₀ h_pos_pow]
    rcases le_or_gt |t| 1 with ht_le | ht_gt
    · have h_pow_le : (1 + |t|) ^ (k + 1) ≤ (2 : ℝ) ^ (k + 1) :=
        pow_le_pow_left₀ h_pos1.le (by linarith) (k + 1)
      calc
        ‖laplaceFourierTransform φ σ t‖ * (1 + |t|) ^ (k + 1)
          ≤ C0 * (2 : ℝ) ^ (k + 1) :=
            mul_le_mul (hC0 σ hσ t) h_pow_le (by positivity) hC0_nonneg
        _ ≤ (2 : ℝ) ^ (k + 1) * C0 + 2 * C1 := by linarith
    · have ht_abs_le_norm : |t| ≤ ‖(σ : ℂ) + (t : ℂ) * I‖ := by
        calc
          |t| = |((σ : ℂ) + (t : ℂ) * I).im| := by simp
          _ ≤ ‖(σ : ℂ) + (t : ℂ) * I‖ := Complex.abs_im_le_norm _
      have h_ibp := mul_laplaceFourierTransform_eq_deriv hφ_diff1 hφ_supp σ t
      have h_mul_norm :
          |t| * ‖laplaceFourierTransform φ σ t‖ ≤ ‖laplaceFourierTransform (deriv φ) σ t‖ := by
        calc
          |t| * ‖laplaceFourierTransform φ σ t‖
            ≤ ‖(σ : ℂ) + (t : ℂ) * I‖ * ‖laplaceFourierTransform φ σ t‖ :=
              mul_le_mul_of_nonneg_right ht_abs_le_norm (norm_nonneg _)
          _ = ‖((σ : ℂ) + (t : ℂ) * I) * laplaceFourierTransform φ σ t‖ := (norm_mul _ _).symm
          _ = ‖laplaceFourierTransform (deriv φ) σ t‖ := by rw [h_ibp]
      have h_ih := (le_div_iff₀ (by positivity : 0 < (1 + |t|) ^ k)).mp (hC1 σ hσ t)
      have h1t_le : 1 + |t| ≤ 2 * |t| := by linarith
      calc
        ‖laplaceFourierTransform φ σ t‖ * (1 + |t|) ^ (k + 1)
          = ‖laplaceFourierTransform φ σ t‖ * (1 + |t|) ^ k * (1 + |t|) := by
            rw [pow_succ]; ring
        _ ≤ ‖laplaceFourierTransform φ σ t‖ * (1 + |t|) ^ k * (2 * |t|) :=
            mul_le_mul_of_nonneg_left h1t_le (by positivity)
        _ = 2 * ((|t| * ‖laplaceFourierTransform φ σ t‖) * (1 + |t|) ^ k) := by ring
        _ ≤ 2 * (‖laplaceFourierTransform (deriv φ) σ t‖ * (1 + |t|) ^ k) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right h_mul_norm (by positivity)) (by positivity)
        _ ≤ 2 * C1 := mul_le_mul_of_nonneg_left h_ih (by positivity)
        _ ≤ (2 : ℝ) ^ (k + 1) * C0 + 2 * C1 := by
          have : 0 ≤ (2 : ℝ) ^ (k + 1) * C0 := by positivity
          linarith

/-- Continuity of `laplaceFourierTransform φ σ` in $t \in \mathbb{R}$ for a compactly supported
continuous function $\varphi$. -/
theorem continuous_laplaceFourierTransform {φ : ℝ → ℝ}
    (hφ_cont : Continuous φ) (hφ_supp : HasCompactSupport φ) (σ : ℝ) :
    Continuous (laplaceFourierTransform φ σ) := by
  unfold laplaceFourierTransform
  refine continuous_of_dominated
    (bound := fun h : ℝ => ‖φ h‖ * Real.exp (-h * σ)) ?_ ?_ ?_ ?_
  · intro t
    fun_prop
  · intro t
    filter_upwards with h
    rw [norm_mul, Complex.norm_real, Complex.norm_exp]
    have h_re : (- (h : ℂ) * ((σ : ℂ) + (t : ℂ) * I)).re = -h * σ := by
      simp [Complex.mul_re]
    rw [h_re]
  · have h_cont_bound : Continuous (fun h : ℝ => ‖φ h‖ * Real.exp (-h * σ)) := by fun_prop
    have h_supp_bound : HasCompactSupport (fun h : ℝ => ‖φ h‖ * Real.exp (-h * σ)) :=
      hφ_supp.norm.mul_right
    exact h_cont_bound.integrable_of_hasCompactSupport h_supp_bound
  · filter_upwards with h
    fun_prop

/-- Integrability of `laplaceFourierTransform φ σ` on $\mathbb{R}$ for a compactly supported
smooth function $\varphi$. -/
theorem integrable_laplaceFourierTransform {φ : ℝ → ℝ}
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_supp : HasCompactSupport φ) (σ : ℝ) :
    Integrable (laplaceFourierTransform φ σ) := by
  obtain ⟨C, hC_nonneg, hC⟩ :=
    exists_bound_laplaceFourierTransform 2 (hφ_smooth.of_le (by simp))
      hφ_supp σ σ
  have h_meas : AEStronglyMeasurable (laplaceFourierTransform φ σ) volume :=
    (continuous_laplaceFourierTransform hφ_smooth.continuous hφ_supp σ).aestronglyMeasurable
  refine (integrable_inv_one_add_sq.const_mul C).mono' h_meas ?_
  filter_upwards with t
  have ht_bound := hC σ (left_mem_Icc.mpr le_rfl) t
  have h_sq_le : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by
    have : 0 ≤ |t| := abs_nonneg t
    nlinarith [sq_abs t]
  have h_pos : 0 < 1 + t ^ 2 := by positivity
  calc
    ‖laplaceFourierTransform φ σ t‖
      ≤ C / (1 + |t|) ^ 2 := ht_bound
    _ ≤ C / (1 + t ^ 2) := div_le_div_of_nonneg_left hC_nonneg h_pos h_sq_le
    _ = C * (1 + t ^ 2)⁻¹ := div_eq_mul_inv _ _

/-- Orthogonality of integer Fourier modes on $[-\pi, \pi]$:
$$\int_{-\pi}^{\pi} e^{i n \theta} \, d\theta =
  \begin{cases} 2\pi & n = 0, \\ 0 & n \ne 0. \end{cases}$$ -/
lemma integral_exp_int_mul_I (n : ℤ) :
    (∫ θ in (-π)..π, Complex.exp ((n : ℂ) * (θ : ℂ) * I)) =
      if n = 0 then (2 * π : ℂ) else 0 := by
  split_ifs with hn
  · subst hn
    simp [intervalIntegral.integral_const]
    ring
  · have hn_c : (n : ℂ) * I ≠ 0 :=
      mul_ne_zero (Int.cast_ne_zero.mpr hn) I_ne_zero
    have h_deriv : ∀ θ ∈ uIcc (-π) π,
        HasDerivAt (fun x : ℝ => Complex.exp ((n : ℂ) * (x : ℂ) * I) / ((n : ℂ) * I))
          (Complex.exp ((n : ℂ) * (θ : ℂ) * I)) θ := by
      intro θ _
      have h1 : HasDerivAt (fun x : ℝ => (n : ℂ) * (x : ℂ) * I) ((n : ℂ) * I) θ := by
        simpa [mul_assoc] using
          (((hasDerivAt_id θ).ofReal_comp).const_mul (n : ℂ)).mul_const I
      simpa [mul_div_cancel_right₀ _ hn_c] using (h1.cexp).div_const ((n : ℂ) * I)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv
      ((by fun_prop : Continuous _).intervalIntegrable _ _)]
    have h_per : Complex.exp ((n : ℂ) * (π : ℂ) * I) =
        Complex.exp ((n : ℂ) * ((-π : ℝ) : ℂ) * I) := by
      have h_eq : (n : ℂ) * (π : ℂ) * I =
          (n : ℂ) * ((-π : ℝ) : ℂ) * I + (n : ℂ) * (2 * π * I) := by
        push_cast; ring
      rw [h_eq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [h_per, sub_self]

namespace MonomialFourPointData

variable (M : MonomialFourPointData)

/-!
## Stage A: Spin-$J$ Fourier Projection on $[-\pi, \pi]$ and Folding to $[-\pi/2, \pi/2]$
-/

/-- The integrand of the spin-$J$ inverse Fourier projection at $(w_l, w_r)$ and angle $\theta$:
$$e^{-J (w_r + i\theta)} \, \mathcal{G}_{\text{mon}}(w_l - i\theta, w_r + i\theta).$$ -/
noncomputable def fourierIntegrand (J : ℤ) (wl wr : ℂ) (θ : ℝ) : ℂ :=
  Complex.exp (- (J : ℂ) * (wr + (θ : ℂ) * I)) *
    M.eval (wl - (θ : ℂ) * I) (wr + (θ : ℂ) * I)

/-- Opposite imaginary shifts $(w_l - i\theta, w_r + i\theta)$ preserve membership in `UcDisk`. -/
lemma sub_I_mul_mem_UcDisk {w : ℂ} (hw : w ∈ UcDisk) (θ : ℝ) :
    w - (θ : ℂ) * I ∈ UcDisk := by
  rw [mem_UcDisk_iff] at hw ⊢
  simpa using hw

lemma add_I_mul_mem_UcDisk {w : ℂ} (hw : w ∈ UcDisk) (θ : ℝ) :
    w + (θ : ℂ) * I ∈ UcDisk := by
  rw [mem_UcDisk_iff] at hw ⊢
  simpa using hw

/-- For even spin $J$, `fourierIntegrand` is $\pi$-periodic in $\theta$:
$$F_J(\theta + \pi) = F_J(\theta).$$ -/
theorem fourierIntegrand_add_pi {J : ℤ} (hJ : Even J) (wl wr : ℂ) (θ : ℝ) :
    M.fourierIntegrand J wl wr (θ + π) = M.fourierIntegrand J wl wr θ := by
  rcases hJ with ⟨k, rfl⟩
  dsimp [fourierIntegrand]
  have h_wl : wl - ((θ + π : ℝ) : ℂ) * I = (wl - (θ : ℂ) * I) - π * I := by
    push_cast; ring
  have h_wr : wr + ((θ + π : ℝ) : ℂ) * I = (wr + (θ : ℂ) * I) + π * I := by
    push_cast; ring
  rw [h_wl, h_wr, M.eval_shift_pi]
  congr 1
  have h_exp :
      - ((k + k : ℤ) : ℂ) * (wr + (θ : ℂ) * I + π * I) =
      - ((k + k : ℤ) : ℂ) * (wr + (θ : ℂ) * I) + ((-k : ℤ) : ℂ) * (2 * π * I) := by
    push_cast; ring
  rw [h_exp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **The $s$-channel positivity bound on the Fourier integrand**: for all $(w_l, w_r) \in
\operatorname{UcPdisk}$ and $\theta \in \mathbb{R}$,
$$\left\|e^{-J (w_r + i\theta)} \mathcal{G}_{\text{mon}}(w_l - i\theta, w_r + i\theta)\right\| \le
  e^{-J \operatorname{Re}(w_r)} \mathcal{G}_{\text{mon}}(\operatorname{Re}(w_l),
  \operatorname{Re}(w_r)).$$ -/
theorem norm_fourierIntegrand_le (J : ℤ) {wl wr : ℂ}
    (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) (θ : ℝ) :
    ‖M.fourierIntegrand J wl wr θ‖ ≤
      Real.exp (- (J : ℝ) * wr.re) * M.evalReal wl.re wr.re := by
  dsimp [fourierIntegrand]
  rw [norm_mul, Complex.norm_exp]
  have h_re_exp : (- (J : ℂ) * (wr + (θ : ℂ) * I)).re = - (J : ℝ) * wr.re := by
    simp [Complex.mul_re]
  rw [h_re_exp]
  have h_bound := M.norm_eval_le_evalReal (sub_I_mul_mem_UcDisk hwl θ) (add_I_mul_mem_UcDisk hwr θ)
  have h_wl_re : (wl - (θ : ℂ) * I).re = wl.re := by simp
  have h_wr_re : (wr + (θ : ℂ) * I).re = wr.re := by simp
  rw [h_wl_re, h_wr_re] at h_bound
  exact mul_le_mul_of_nonneg_left h_bound (Real.exp_pos _).le

/-- Full spin-$J$ inverse Fourier projection over $\theta \in [-\pi, \pi]$:
$$\int_{-\pi}^{\pi} \frac{d\theta}{2\pi} \,
  e^{-J (w_r + i\theta)} \, \mathcal{G}_{\text{mon}}(w_l - i\theta, w_r + i\theta).$$ -/
noncomputable def fourierProjSpinFull (J : ℤ) (wl wr : ℂ) : ℂ :=
  (2 * π : ℂ)⁻¹ * ∫ θ in (-π)..π, M.fourierIntegrand J wl wr θ

/-- Folded spin-$J$ inverse Fourier projection over the half-interval
$\theta \in [-\pi/2, \pi/2]$:
$$\int_{-\pi/2}^{\pi/2} \frac{d\theta}{\pi} \,
  e^{-J (w_r + i\theta)} \, \mathcal{G}_{\text{mon}}(w_l - i\theta, w_r + i\theta).$$ -/
noncomputable def fourierProjSpin (J : ℤ) (wl wr : ℂ) : ℂ :=
  (π : ℂ)⁻¹ * ∫ θ in (-π / 2)..(π / 2), M.fourierIntegrand J wl wr θ

/-- Continuity of `fourierIntegrand` in $\theta \in \mathbb{R}$ for
$(w_l, w_r) \in \operatorname{UcPdisk}$. -/
theorem continuous_fourierIntegrand (J : ℤ) {wl wr : ℂ}
    (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) :
    Continuous (M.fourierIntegrand J wl wr) := by
  have h1 : Continuous (fun θ : ℝ => Complex.exp (- (J : ℂ) * (wr + (θ : ℂ) * I))) := by fun_prop
  exact h1.mul (M.continuous_eval_shift hwl hwr)

/-- For even spin $J$, the $\pi$-periodicity of `fourierIntegrand` folds the full integral over
$[-\pi, \pi]$ onto twice the half-interval $[-\pi/2, \pi/2]$. -/
theorem fourierProjSpinFull_eq_fourierProjSpin {J : ℤ} (hJ : Even J) {wl wr : ℂ}
    (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) :
    M.fourierProjSpinFull J wl wr = M.fourierProjSpin J wl wr := by
  dsimp [fourierProjSpinFull, fourierProjSpin]
  have h_cont := M.continuous_fourierIntegrand J hwl hwr
  have h_per : Function.Periodic (M.fourierIntegrand J wl wr) π :=
    M.fourierIntegrand_add_pi hJ wl wr
  have h_shift := h_per.intervalIntegral_add_eq (-π) (-π / 2)
  have ha : -π + π = (0 : ℝ) := by ring
  have hb : -π / 2 + π = π / 2 := by ring
  rw [ha, hb] at h_shift
  have h_split_full := intervalIntegral.integral_add_adjacent_intervals
    (h_cont.intervalIntegrable (μ := volume) (-π) 0)
    (h_cont.intervalIntegrable (μ := volume) 0 π)
  have h_shift2 := h_per.intervalIntegral_add_eq 0 (-π)
  have hb2 : 0 + π = π := by ring
  rw [hb2, ha] at h_shift2
  have h_double :
      (∫ θ in (-π)..π, M.fourierIntegrand J wl wr θ) =
        2 * ∫ θ in (-π / 2)..(π / 2), M.fourierIntegrand J wl wr θ := by
    linear_combination -h_split_full + h_shift2 + 2 * h_shift
  rw [h_double]
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-- Exact spin-$J$ Fourier projection on the full interval $[-\pi, \pi]$: for any
$(w_l, w_r) \in \operatorname{UcPdisk}$,
$$L_J(w_l + w_r) = \int_{-\pi}^{\pi} \frac{d\theta}{2\pi} \,
  e^{-J (w_r + i\theta)} \, \mathcal{G}_{\text{mon}}(w_l - i\theta, w_r + i\theta).$$ -/
theorem laplaceSpin_eq_fourierProjSpinFull (J : ℤ) {wl wr : ℂ}
    (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) :
    M.laplaceSpin J (wl + wr) = M.fourierProjSpinFull J wl wr := by
  set F : ℤ → ℝ → ℂ := fun J' θ =>
    Complex.exp (- (J : ℂ) * (wr + (θ : ℂ) * I)) *
      M.evalSpin J' (wl - (θ : ℂ) * I) (wr + (θ : ℂ) * I)
  set bound : ℤ → ℝ → ℝ := fun J' _ =>
    Real.exp (- (J : ℝ) * wr.re) * M.evalSpinReal J' wl.re wr.re
  have h_hasSum_int :
      HasSum (fun J' : ℤ => ∫ θ in (-π)..π, F J' θ)
        (∫ θ in (-π)..π, M.fourierIntegrand J wl wr θ) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
      bound ?_ ?_ ?_ ?_ ?_
    · intro J'
      have h_cont : Continuous (F J') :=
        (by fun_prop : Continuous (fun θ : ℝ => Complex.exp (- (J : ℂ) * (wr + (θ : ℂ) * I)))).mul
          (M.continuous_evalSpin_shift hwl hwr J')
      exact h_cont.aestronglyMeasurable
    · intro J'
      filter_upwards with θ _
      dsimp [F, bound]
      rw [norm_mul, Complex.norm_exp]
      have h_re_exp : (- (J : ℂ) * (wr + (θ : ℂ) * I)).re = - (J : ℝ) * wr.re := by
        simp [Complex.mul_re]
      rw [h_re_exp]
      have h_le := M.norm_evalSpin_le_evalSpinReal J' (wl - (θ : ℂ) * I) (wr + (θ : ℂ) * I)
      have h_wl_re : (wl - (θ : ℂ) * I).re = wl.re := by simp
      have h_wr_re : (wr + (θ : ℂ) * I).re = wr.re := by simp
      rw [h_wl_re, h_wr_re] at h_le
      exact mul_le_mul_of_nonneg_left h_le (Real.exp_pos _).le
    · filter_upwards with θ _
      exact (M.summable_real hwl hwr).mul_left _
    · exact intervalIntegrable_const
        (c := ∑' J' : ℤ, Real.exp (- (J : ℝ) * wr.re) * M.evalSpinReal J' wl.re wr.re)
    · filter_upwards with θ _
      dsimp [F, fourierIntegrand, eval]
      exact (M.summable_evalSpin (sub_I_mul_mem_UcDisk hwl θ)
        (add_I_mul_mem_UcDisk hwr θ)).hasSum.mul_left _
  have h_term : ∀ J' : ℤ,
      (∫ θ in (-π)..π, F J' θ) =
        if J' = J then (2 * π : ℂ) * M.laplaceSpin J (wl + wr) else 0 := by
    intro J'
    have h_eq : ∀ θ : ℝ, F J' θ =
        (Complex.exp (((J' - J : ℤ) : ℂ) * wr) * M.laplaceSpin J' (wl + wr)) *
          Complex.exp (((J' - J : ℤ) : ℂ) * (θ : ℂ) * I) := by
      intro θ
      dsimp [F]
      rw [M.evalSpin_eq_exp_mul_laplace J' (wl - (θ : ℂ) * I) (wr + (θ : ℂ) * I)]
      have h_add : (wl - (θ : ℂ) * I) + (wr + (θ : ℂ) * I) = wl + wr := by ring
      rw [h_add]
      have h_exp :
          Complex.exp (- (J : ℂ) * (wr + (θ : ℂ) * I)) *
            Complex.exp ((J' : ℂ) * (wr + (θ : ℂ) * I)) =
          Complex.exp (((J' - J : ℤ) : ℂ) * wr) *
            Complex.exp (((J' - J : ℤ) : ℂ) * (θ : ℂ) * I) := by
        rw [← Complex.exp_add, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      linear_combination h_exp * M.laplaceSpin J' (wl + wr)
    simp_rw [h_eq, intervalIntegral.integral_const_mul, integral_exp_int_mul_I (J' - J),
      sub_eq_zero]
    split_ifs with hJ'
    · subst hJ'
      simp [mul_comm]
    · simp
  simp_rw [h_term] at h_hasSum_int
  have h_int_eq :
      (∫ θ in (-π)..π, M.fourierIntegrand J wl wr θ) =
        (2 * π : ℂ) * M.laplaceSpin J (wl + wr) :=
    h_hasSum_int.unique (hasSum_ite_eq J ((2 * π : ℂ) * M.laplaceSpin J (wl + wr)))
  dsimp [fourierProjSpinFull]
  rw [h_int_eq, inv_mul_cancel_left₀]
  exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)

/-- Exact spin-$J$ Fourier projection on the folded half-interval $[-\pi/2, \pi/2]$ for even $J$:
$$L_J(w_l + w_r) = \int_{-\pi/2}^{\pi/2} \frac{d\theta}{\pi} \,
  e^{-J (w_r + i\theta)} \, \mathcal{G}_{\text{mon}}(w_l - i\theta, w_r + i\theta).$$ -/
theorem laplaceSpin_eq_fourierProjSpin {J : ℤ} (hJ : Even J) {wl wr : ℂ}
    (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) :
    M.laplaceSpin J (wl + wr) = M.fourierProjSpin J wl wr := by
  rw [M.laplaceSpin_eq_fourierProjSpinFull J hwl hwr,
    M.fourierProjSpinFull_eq_fourierProjSpin hJ hwl hwr]

/-- Real-axis specialization of `laplaceSpin_eq_fourierProjSpin`: for even $J$ and real
$\sigma_l < 0, \sigma_r < 0$, the real spin-$J$ Laplace transform $L_J(\sigma_l + \sigma_r)$ is
given by the folded $\theta$-integral on $[-\pi/2, \pi/2]$ along $(\sigma_l - i\theta,
\sigma_r + i\theta)$, where both arguments stay strictly inside the $t$-channel strip
$\operatorname{Im} \in (-\pi, \pi)$. -/
theorem laplaceSpinReal_eq_fourierProjSpin {J : ℤ} (hJ : Even J) {σl σr : ℝ}
    (hσl : σl < 0) (hσr : σr < 0) :
    (M.laplaceSpinReal J (σl + σr) : ℂ) = M.fourierProjSpin J (σl : ℂ) (σr : ℂ) := by
  have hwl : (σl : ℂ) ∈ UcDisk := by rw [mem_UcDisk_iff]; simpa using hσl
  have hwr : (σr : ℂ) ∈ UcDisk := by rw [mem_UcDisk_iff]; simpa using hσr
  rw [← M.laplaceSpin_ofReal, Complex.ofReal_add, M.laplaceSpin_eq_fourierProjSpin hJ hwl hwr]

/-!
## Stage B: Pairing with a Test Function $\varphi(h)$ via Vertical Contour Integration of $L_J(w)$
-/

/-- The pairing $\int_{\mathbb{R}} \varphi(h) \, d\mu_J(h)$ of a test function
$\varphi : \mathbb{R} \to \mathbb{R}$ with the spin-$J$ spectral measure $\mu_J$. -/
noncomputable def pairSpin (J : ℤ) (φ : ℝ → ℝ) : ℝ :=
  ∫ h : ℝ, φ h ∂(M.mu J)

theorem pairSpin_of_odd {J : ℤ} (hJ : Odd J) (φ : ℝ → ℝ) :
    M.pairSpin J φ = 0 := by
  dsimp [pairSpin]
  rw [M.support_odd_spin J hJ, integral_zero_measure]

/-- 1D Fourier inversion for `laplaceFourierTransform`: for a compactly supported smooth test
function $\varphi : \mathbb{R} \to \mathbb{R}$ and any $\sigma, h \in \mathbb{R}$,
$$\int_{-\infty}^{\infty} \frac{dt}{2\pi} \, \widehat{\varphi}_{\sigma}(t) \, e^{h(\sigma + i t)} =
  \varphi(h).$$ -/
theorem integral_laplaceFourierTransform_mul_exp {φ : ℝ → ℝ}
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_supp : HasCompactSupport φ)
    (σ h : ℝ) :
    (2 * π : ℂ)⁻¹ *
        (∫ t : ℝ, laplaceFourierTransform φ σ t *
          Complex.exp ((h : ℂ) * ((σ : ℂ) + (t : ℂ) * I))) =
      (φ h : ℂ) := by
  set f : ℝ → ℂ := fun x => (φ x : ℂ) * Complex.exp (- (x : ℂ) * (σ : ℂ))
  have hf_cont : Continuous f := by
    have : Continuous φ := hφ_smooth.continuous
    dsimp [f]; fun_prop
  have hf_supp : HasCompactSupport f :=
    (hφ_supp.comp_left Complex.ofReal_zero).mul_right
  have hf_int : Integrable f := hf_cont.integrable_of_hasCompactSupport hf_supp
  have h_fourier : ∀ u : ℝ, 𝓕 f u = laplaceFourierTransform φ σ (2 * π * u) := by
    intro u
    rw [Real.fourier_eq']
    unfold laplaceFourierTransform
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp [f]
    rw [mul_comm (Complex.exp _), mul_assoc, ← Complex.exp_add]
    congr 2
    simp
    ring
  have h2pi_ne : (2 * π : ℝ) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  have h2pi_pos : (0 : ℝ) < 2 * π := by positivity
  have h_fourier_int : Integrable (𝓕 f) := by
    rw [funext h_fourier]
    exact (integrable_laplaceFourierTransform hφ_smooth hφ_supp σ).comp_mul_left' h2pi_ne
  have h_inv : 𝓕⁻ (𝓕 f) h = f h :=
    hf_int.fourierInv_fourier_eq h_fourier_int hf_cont.continuousAt
  rw [Real.fourierInv_eq'] at h_inv
  simp_rw [h_fourier, smul_eq_mul] at h_inv
  let g : ℝ → ℂ := fun t =>
    Complex.exp ((h : ℂ) * (t : ℂ) * I) * laplaceFourierTransform φ σ t
  have h_inv_g : (∫ u : ℝ, g (2 * π * u)) = f h := by
    rw [← h_inv]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp [g]
    congr 2
    simp
    ring
  rw [Measure.integral_comp_mul_left g (2 * π), abs_of_pos (inv_pos.mpr h2pi_pos),
    Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat] at h_inv_g
  have h_int_split :
      (∫ t : ℝ, laplaceFourierTransform φ σ t *
        Complex.exp ((h : ℂ) * ((σ : ℂ) + (t : ℂ) * I))) =
      Complex.exp ((h : ℂ) * (σ : ℂ)) * ∫ t : ℝ, g t := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    dsimp [g]
    have h_exp : Complex.exp ((h : ℂ) * ((σ : ℂ) + (t : ℂ) * I)) =
        Complex.exp ((h : ℂ) * (σ : ℂ)) * Complex.exp ((h : ℂ) * (t : ℂ) * I) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [h_exp]
    ring
  rw [h_int_split, ← mul_assoc, mul_comm (2 * π : ℂ)⁻¹, mul_assoc, h_inv_g]
  dsimp [f]
  rw [mul_comm (φ h : ℂ), ← mul_assoc, ← Complex.exp_add]
  have h_add : (h : ℂ) * (σ : ℂ) + - (h : ℂ) * (σ : ℂ) = 0 := by ring
  rw [h_add, Complex.exp_zero, one_mul]

/-- Fourier inversion relating `pairSpin` to the vertical contour integral of the single-variable
spin-$J$ Laplace transform $L_J(\sigma + i t) = \operatorname{laplaceSpin} J (\sigma + i t)$
against `laplaceFourierTransform` for any $\sigma < 0$:
$$\int_{\mathbb{R}} \varphi(h) \, d\mu_J(h) =
  \int_{-\infty}^{\infty} \frac{dt}{2\pi} \,
    \widehat{\varphi}_{\sigma}(t) \, L_J(\sigma + i t).$$ -/
theorem pairSpin_eq_integral_laplaceSpin (J : ℤ) {φ : ℝ → ℝ}
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_supp : HasCompactSupport φ)
    {σ : ℝ} (hσ : σ < 0) :
    (M.pairSpin J φ : ℂ) =
      (2 * π : ℂ)⁻¹ * ∫ t : ℝ,
        laplaceFourierTransform φ σ t * M.laplaceSpin J ((σ : ℂ) + (t : ℂ) * I) := by
  let F : ℝ → ℝ → ℂ := fun t h =>
    laplaceFourierTransform φ σ t * Complex.exp ((h : ℂ) * ((σ : ℂ) + (t : ℂ) * I))
  have hF_cont : Continuous (Function.uncurry F) := by
    have h1 : Continuous (fun z : ℝ × ℝ => laplaceFourierTransform φ σ z.1) :=
      (continuous_laplaceFourierTransform hφ_smooth.continuous hφ_supp σ).comp continuous_fst
    have h2 : Continuous (fun z : ℝ × ℝ =>
        Complex.exp ((z.2 : ℂ) * ((σ : ℂ) + (z.1 : ℂ) * I))) := by fun_prop
    exact h1.mul h2
  have hF_int : Integrable (Function.uncurry F) (volume.prod (M.mu J)) := by
    have h_dom : Integrable
        (fun z : ℝ × ℝ => ‖laplaceFourierTransform φ σ z.1‖ * Real.exp (z.2 * σ))
        (volume.prod (M.mu J)) :=
      (integrable_laplaceFourierTransform hφ_smooth hφ_supp σ).norm.mul_prod
        (M.integrable_exp_real hσ J)
    refine h_dom.mono' hF_cont.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    dsimp [Function.uncurry, F]
    rw [norm_mul, Complex.norm_exp]
    have h_re : ((z.2 : ℂ) * ((σ : ℂ) + (z.1 : ℂ) * I)).re = z.2 * σ := by
      simp [Complex.mul_re]
    rw [h_re]
  have h_inner : ∀ t : ℝ,
      laplaceFourierTransform φ σ t * M.laplaceSpin J ((σ : ℂ) + (t : ℂ) * I) =
        ∫ h : ℝ, F t h ∂(M.mu J) := by
    intro t
    dsimp [laplaceSpin, F]
    rw [← integral_const_mul]
  simp_rw [h_inner]
  rw [integral_integral_swap hF_int, ← integral_const_mul]
  dsimp [F]
  simp_rw [integral_laplaceFourierTransform_mul_exp hφ_smooth hφ_supp σ]
  dsimp [pairSpin]
  exact integral_ofReal.symm

end MonomialFourPointData

