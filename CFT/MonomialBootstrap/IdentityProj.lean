/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Balt van Rees
-/
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import CFT.MonomialBootstrap.Gap

/-!
# Explicit $t$-Channel Identity Integrals and Universal Large-Spin Limits

This file defines the $t$-channel identity spin projection `identityProjSpin` and the universal
large-spin Laplace and spectral limits (`universalLaplace`, `universalLaplaceReal`, and
`universalMonomialPairing`), and proves the two explicit $t$-channel identity integral theorems:

1. **Vertical Laplace–Fourier Integral of `universalLaplace`**
   (`integral_laplaceFourierTransform_mul_universalLaplace`):
   Expanding $(1 - e^w)^{-2\Delta_\phi} = \sum_{n=0}^{\infty} \frac{(2\Delta_\phi)_n}{n!} e^{n w}$
   on $\operatorname{UcDisk}$ and integrating term-by-term against `laplaceFourierTransform φ σ t`
   recovers the universal double-twist spectral pairing `universalMonomialPairing Δ_phi φ`.

2. **Large-Spin Asymptotics of `identityProjSpin` on the Real Axis**
   (`tendsto_identityProjSpin_real`):
   Along the real-axis contour $\sigma_l = \sigma + 1/(2k), \sigma_r = -1/(2k)$ ($\sigma < 0$),
   splitting the folded $[-\pi/2, \pi/2]$ integral into the full $[-\pi, \pi]$ integral
   (`identityProjSpinFull`, evaluated via diagonal binomial series, Euler's Gamma limit, and
   Tannery's theorem) minus the outer $[-\pi, -\pi/2] \cup [\pi/2, \pi]$ integral (bounded by
   $O(1/(2k))$ via integration by parts) proves that
   $$\lim_{k \to \infty} (2k)^{1 - 2\Delta_\phi}
     \operatorname{identityProjSpin}\!\left(\Delta_\phi, 2k,
       \sigma + \frac{1}{2k}, -\frac{1}{2k}\right)
     = \operatorname{universalLaplaceReal}(\Delta_\phi, \sigma).$$
-/

open Real Complex Topology Set Metric MeasureTheory Filter
open scoped ComplexConjugate

/-!
## Universal Asymptotic Spin-$J$ Laplace Transform and Spectral Pairing
-/

/-- The folded $\theta$-integral of the $t$-channel identity contribution `crossIdentity Δ_phi`
over $\theta \in [-\pi/2, \pi/2]$:
$$\int_{-\pi/2}^{\pi/2} \frac{d\theta}{\pi} \,
  e^{-J (w_r + i\theta)} \, \mathcal{G}_{\text{id}}(w_l - i\theta, w_r + i\theta).$$ -/
noncomputable def identityProjSpin (Δ_phi : ℝ) (J : ℤ) (wl wr : ℂ) : ℂ :=
  (π : ℂ)⁻¹ * ∫ θ in (-π / 2)..(π / 2),
    Complex.exp (- (J : ℂ) * (wr + (θ : ℂ) * I)) *
      crossIdentity Δ_phi (wl - (θ : ℂ) * I) (wr + (θ : ℂ) * I)

/-- The universal large-spin limit $L_{\text{id}}(\Delta_\phi, w)$ of the rescaled spin-$J$
Laplace transform $(2k)^{1 - 2\Delta_\phi} L_{2k}(w)$ on $w \in \operatorname{UcDisk}$:
$$L_{\text{id}}(\Delta_\phi, w) =
  \frac{2 \cdot 4^{\Delta_\phi}}{\Gamma(2\Delta_\phi)}
  \operatorname{crossFactor}(\Delta_\phi, w) =
  \frac{2 \cdot 4^{2\Delta_\phi}}{\Gamma(2\Delta_\phi)}
  e^{\Delta_\phi w} (1 - e^w)^{-2\Delta_\phi}.$$ -/
noncomputable def universalLaplace (Δ_phi : ℝ) (w : ℂ) : ℂ :=
  ((2 * (4 : ℝ) ^ Δ_phi / Real.Gamma (2 * Δ_phi) : ℝ) : ℂ) * crossFactor Δ_phi w

/-- The real-valued universal large-spin Laplace transform $L_{\text{id}}(\Delta_\phi, \sigma)$
for $\sigma < 0$:
$$L_{\text{id}}(\Delta_\phi, \sigma) =
  \frac{2 \cdot 4^{2\Delta_\phi}}{\Gamma(2\Delta_\phi)}
  e^{\Delta_\phi \sigma} (1 - e^\sigma)^{-2\Delta_\phi}.$$ -/
noncomputable def universalLaplaceReal (Δ_phi : ℝ) (σ : ℝ) : ℝ :=
  (2 * (4 : ℝ) ^ (2 * Δ_phi) / Real.Gamma (2 * Δ_phi)) *
    Real.exp (Δ_phi * σ) * (1 - Real.exp σ) ^ (- (2 * Δ_phi))

/-- The universal large-spin monomial spectral pairing for external dimension $\Delta_\phi$:
$$\frac{2 \cdot 4^{2\Delta_\phi}}{\Gamma(2\Delta_\phi)}
  \sum_{n=0}^{\infty} \frac{(2\Delta_\phi)_n}{n!} \, \varphi(\Delta_\phi + n).$$ -/
noncomputable def universalMonomialPairing (Δ_phi : ℝ) (φ : ℝ → ℝ) : ℝ :=
  (2 * (4 : ℝ) ^ (2 * Δ_phi) / Real.Gamma (2 * Δ_phi)) *
    ∑' n : ℕ, (realPochhammer (2 * Δ_phi) n / (Nat.factorial n : ℝ)) * φ (Δ_phi + (n : ℝ))

/-- On the negative real axis $\sigma < 0$, `universalLaplace Δ_phi (σ : ℂ)` coincides with
`(universalLaplaceReal Δ_phi σ : ℂ)`. -/
theorem universalLaplace_ofReal (Δ_phi : ℝ) {σ : ℝ} (hσ : σ < 0) :
    universalLaplace Δ_phi (σ : ℂ) = (universalLaplaceReal Δ_phi σ : ℂ) := by
  dsimp [universalLaplace, universalLaplaceReal, crossFactor]
  have h1q_pos : 0 < 1 - Real.exp σ := by
    have : Real.exp σ < 1 := Real.exp_lt_one_iff.mpr hσ
    linarith
  have h4_cast : (4 : ℂ) ^ (Δ_phi : ℂ) = (((4 : ℝ) ^ Δ_phi : ℝ) : ℂ) := by
    have : (4 : ℂ) = ((4 : ℝ) : ℂ) := by norm_cast
    rw [this, ← Complex.ofReal_cpow (by norm_num)]
  have hexp_cast : Complex.exp ((Δ_phi : ℂ) * (σ : ℂ)) = ((Real.exp (Δ_phi * σ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Complex.ofReal_exp]
  have h1q_cast :
      (1 - Complex.exp (σ : ℂ)) ^ (- (2 * Δ_phi : ℂ)) =
        (((1 - Real.exp σ) ^ (- (2 * Δ_phi)) : ℝ) : ℂ) := by
    have h_sub : 1 - Complex.exp (σ : ℂ) = ((1 - Real.exp σ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_exp]; push_cast; rfl
    have h_exp : (- (2 * Δ_phi : ℂ)) = ((- (2 * Δ_phi) : ℝ) : ℂ) := by push_cast; rfl
    rw [h_sub, h_exp, ← Complex.ofReal_cpow h1q_pos.le]
  rw [h4_cast, hexp_cast, h1q_cast]
  norm_cast
  have h4_sq : (4 : ℝ) ^ (2 * Δ_phi) = (4 : ℝ) ^ Δ_phi * (4 : ℝ) ^ Δ_phi := by
    rw [← Real.rpow_add (by norm_num), two_mul]
  rw [h4_sq]
  ring

/-- Continuity of `crossFactor Δ_phi` on `UcDisk`. -/
lemma continuousOn_crossFactor (Δ_phi : ℝ) :
    ContinuousOn (crossFactor Δ_phi) UcDisk := by
  intro w hw
  have h_exp : DifferentiableAt ℂ (fun z => Complex.exp ((Δ_phi : ℂ) * z)) w :=
    (differentiableAt_id.const_mul (Δ_phi : ℂ)).cexp
  have h_sub : DifferentiableAt ℂ (fun z => 1 - Complex.exp z) w :=
    (differentiableAt_const 1).sub differentiableAt_id.cexp
  have h_cpow : DifferentiableAt ℂ (fun z => (1 - Complex.exp z) ^ (- (2 * Δ_phi : ℂ))) w :=
    h_sub.cpow_const (one_sub_exp_mem_slitPlane hw)
  exact ((h_exp.const_mul _).mul h_cpow).continuousAt.continuousWithinAt

/-- Continuity of the shifted $t$-channel identity contribution
$\theta \mapsto \mathcal{G}_{\text{id}}(w_l - i\theta, w_r + i\theta)$ on $\mathbb{R}$. -/
lemma continuous_crossIdentity_shift (Δ_phi : ℝ) {wl wr : ℂ}
    (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) :
    Continuous (fun θ : ℝ => crossIdentity Δ_phi (wl - (θ : ℂ) * I) (wr + (θ : ℂ) * I)) := by
  have h1 : Continuous (fun θ : ℝ => crossFactor Δ_phi (wl - (θ : ℂ) * I)) :=
    (continuousOn_crossFactor Δ_phi).comp_continuous (by fun_prop)
      (fun θ => MonomialFourPointData.sub_I_mul_mem_UcDisk hwl θ)
  have h2 : Continuous (fun θ : ℝ => crossFactor Δ_phi (wr + (θ : ℂ) * I)) :=
    (continuousOn_crossFactor Δ_phi).comp_continuous (by fun_prop)
      (fun θ => MonomialFourPointData.add_I_mul_mem_UcDisk hwr θ)
  exact h1.mul h2

/-- Lower bound on $\|1 - e^{-\varepsilon + i\theta}\|$ for $0 < \varepsilon \le 1/2$ and
$\theta \in [-\pi/2, \pi/2]$:
$$\frac{e^{-1/2}}{\pi} (\varepsilon + |\theta|) \le \|1 - e^{-\varepsilon + i\theta}\|.$$ -/
lemma norm_one_sub_exp_ge_of_mem_Icc {ε θ : ℝ}
    (hε_pos : 0 < ε) (hε_le : ε ≤ 1 / 2) (hθ : θ ∈ Icc (-π / 2) (π / 2)) :
    Real.exp (-1 / 2) / π * (ε + |θ|) ≤ ‖1 - Complex.exp ((-ε : ℂ) + (θ : ℂ) * I)‖ := by
  set z := Complex.exp ((-ε : ℂ) + (θ : ℂ) * I)
  have hz_norm : ‖z‖ = Real.exp (-ε) := by
    dsimp [z]
    rw [Complex.norm_exp]
    simp
  have h_exp_ge : Real.exp (-1 / 2) ≤ Real.exp (-ε) :=
    Real.exp_le_exp.mpr (by linarith)
  have h_real_part : Real.exp (-1 / 2) * ε ≤ ‖1 - z‖ := by
    have h1 : 1 - Real.exp (-ε) ≤ ‖1 - z‖ := by
      calc
        1 - Real.exp (-ε) = ‖(1 : ℂ)‖ - ‖z‖ := by rw [norm_one, hz_norm]
        _ ≤ ‖(1 : ℂ) - z‖ := norm_sub_norm_le 1 z
    have h2 : ε ≤ Real.exp ε - 1 := by linarith [Real.add_one_le_exp ε]
    have h3 : Real.exp (-ε) * (Real.exp ε - 1) = 1 - Real.exp (-ε) := by
      rw [mul_sub, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    calc
      Real.exp (-1 / 2) * ε ≤ Real.exp (-ε) * (Real.exp ε - 1) :=
        mul_le_mul h_exp_ge h2 hε_pos.le (Real.exp_pos _).le
      _ = 1 - Real.exp (-ε) := h3
      _ ≤ ‖1 - z‖ := h1
  have h_imag_part : Real.exp (-1 / 2) * (2 / π * |θ|) ≤ ‖1 - z‖ := by
    have h_im : |(1 - z).im| = Real.exp (-ε) * |Real.sin θ| := by
      dsimp [z]
      simp [Complex.exp_im, abs_mul, abs_of_pos (Real.exp_pos (-ε))]
    have h_abs_θ : |θ| ≤ π / 2 := abs_le.mpr ⟨by linarith [hθ.1], hθ.2⟩
    have h_sin : 2 / π * |θ| ≤ |Real.sin θ| := Real.mul_abs_le_abs_sin h_abs_θ
    calc
      Real.exp (-1 / 2) * (2 / π * |θ|) ≤ Real.exp (-ε) * |Real.sin θ| :=
        mul_le_mul h_exp_ge h_sin (by positivity) (Real.exp_pos _).le
      _ = |(1 - z).im| := h_im.symm
      _ ≤ ‖1 - z‖ := Complex.abs_im_le_norm (1 - z)
  have h_two_div_pi : 2 / π ≤ 1 :=
    (div_le_one Real.pi_pos).mpr Real.two_le_pi
  have h_real_part' : Real.exp (-1 / 2) * (2 / π * ε) ≤ ‖1 - z‖ := by
    calc
      Real.exp (-1 / 2) * (2 / π * ε) ≤ Real.exp (-1 / 2) * (1 * ε) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right h_two_div_pi hε_pos.le) (Real.exp_pos _).le
      _ = Real.exp (-1 / 2) * ε := by ring
      _ ≤ ‖1 - z‖ := h_real_part
  have h_comb : Real.exp (-1 / 2) / π * (ε + |θ|) =
      (Real.exp (-1 / 2) * (2 / π * ε) + Real.exp (-1 / 2) * (2 / π * |θ|)) / 2 := by ring
  linarith

/-- For $\varepsilon > 0$ and $\alpha \ne -1$, the integral of $(\varepsilon + |\theta|)^\alpha$
over $[-\pi/2, \pi/2]$ is bounded for all $0 < \varepsilon \le 1/2$ by a constant times
$\varepsilon^{\alpha + 1} + 1$. -/
lemma integral_add_abs_rpow_le {α : ℝ} (hα : α ≠ -1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 / 2 →
      (∫ θ in (-π / 2)..(π / 2), (ε + |θ|) ^ α) ≤ C * (ε ^ (α + 1) + 1) := by
  have hα1_ne : α + 1 ≠ 0 := by intro h; apply hα; linarith
  have h_eval : ∀ {ε : ℝ}, 0 < ε →
      (∫ θ in (-π / 2)..(π / 2), (ε + |θ|) ^ α) =
        2 * (((ε + π / 2) ^ (α + 1) - ε ^ (α + 1)) / (α + 1)) := by
    intro ε hε
    have h_cont : Continuous (fun θ : ℝ => (ε + |θ|) ^ α) := by
      refine Continuous.rpow_const (by fun_prop) (fun θ => Or.inl ?_)
      have : 0 < ε + |θ| := by positivity
      exact this.ne'
    have h_split := intervalIntegral.integral_add_adjacent_intervals
      (h_cont.intervalIntegrable (μ := volume) (-π / 2) 0)
      (h_cont.intervalIntegrable (μ := volume) 0 (π / 2))
    have h_neg : (∫ θ in (-π / 2)..0, (ε + |θ|) ^ α) =
        ∫ θ in 0..(π / 2), (ε + |θ|) ^ α := by
      have hcomp := intervalIntegral.integral_comp_neg (fun θ : ℝ => (ε + |θ|) ^ α)
        (a := -π / 2) (b := 0)
      have h_neg_pi : -(-π / 2) = π / 2 := by ring
      rw [h_neg_pi] at hcomp
      simpa [abs_neg] using hcomp
    have h_pos : (∫ θ in 0..(π / 2), (ε + |θ|) ^ α) =
        ∫ θ in 0..(π / 2), (ε + θ) ^ α := by
      refine intervalIntegral.integral_congr (fun θ hθ => ?_)
      rw [uIcc_of_le (by positivity)] at hθ
      simp [abs_of_nonneg hθ.1]
    have h_rpow : (∫ θ in 0..(π / 2), (ε + θ) ^ α) =
        ((ε + π / 2) ^ (α + 1) - ε ^ (α + 1)) / (α + 1) := by
      have hcomp := intervalIntegral.integral_comp_add_left (fun x : ℝ => x ^ α) ε
        (a := 0) (b := π / 2)
      rw [add_zero] at hcomp
      rw [hcomp, integral_rpow (Or.inr ⟨hα, ?_⟩)]
      rw [uIcc_of_le (by linarith [Real.pi_pos])]
      intro h0
      linarith [h0.1]
    rw [← h_split, h_neg, h_pos, h_rpow]
    ring
  rcases lt_or_gt_of_ne hα1_ne with h_neg | h_pos
  · have h_pos_neg : 0 < -(α + 1) := neg_pos.mpr h_neg
    refine ⟨2 / -(α + 1), by positivity, fun {ε} hε_pos _ => ?_⟩
    rw [h_eval hε_pos]
    have h1 : 0 ≤ (ε + π / 2) ^ (α + 1) := by positivity
    have h2 : 0 ≤ ε ^ (α + 1) := by positivity
    have h_div : ((ε + π / 2) ^ (α + 1) - ε ^ (α + 1)) / (α + 1) =
        (ε ^ (α + 1) - (ε + π / 2) ^ (α + 1)) / -(α + 1) := by
      rw [div_neg, ← neg_div, neg_sub]
    rw [h_div]
    calc
      2 * ((ε ^ (α + 1) - (ε + π / 2) ^ (α + 1)) / -(α + 1))
        = (2 / -(α + 1)) * (ε ^ (α + 1) - (ε + π / 2) ^ (α + 1)) := by ring
      _ ≤ (2 / -(α + 1)) * (ε ^ (α + 1) + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · refine ⟨2 * (1 / 2 + π / 2) ^ (α + 1) / (α + 1), by positivity, fun {ε} hε_pos hε_le => ?_⟩
    rw [h_eval hε_pos]
    have h1 : (ε + π / 2) ^ (α + 1) ≤ (1 / 2 + π / 2) ^ (α + 1) :=
      Real.rpow_le_rpow (by positivity) (by linarith) h_pos.le
    have h2 : 0 ≤ ε ^ (α + 1) := by positivity
    calc
      2 * (((ε + π / 2) ^ (α + 1) - ε ^ (α + 1)) / (α + 1))
        = (2 / (α + 1)) * ((ε + π / 2) ^ (α + 1) - ε ^ (α + 1)) := by ring
      _ ≤ (2 / (α + 1)) * ((1 / 2 + π / 2) ^ (α + 1) * (ε ^ (α + 1) + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        nlinarith [show 0 ≤ (1 / 2 + π / 2) ^ (α + 1) by positivity]
      _ = (2 * (1 / 2 + π / 2) ^ (α + 1) / (α + 1)) * (ε ^ (α + 1) + 1) := by ring

/-- Uniform bound on $\int_{-\pi/2}^{\pi/2} \|1 - e^{-\varepsilon + i\theta}\|^\alpha \, d\theta$
for $0 < \varepsilon \le 1/2$ and $\alpha \ne -1$. -/
lemma integral_norm_one_sub_exp_rpow_le {α : ℝ} (hα : α ≠ -1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 / 2 →
      (∫ θ in (-π / 2)..(π / 2), ‖1 - Complex.exp ((-ε : ℂ) + (θ : ℂ) * I)‖ ^ α) ≤
        C * (ε ^ (α + 1) + 1) := by
  have h_cont_lhs : ∀ {ε : ℝ}, 0 < ε →
      Continuous (fun θ : ℝ => ‖1 - Complex.exp ((-ε : ℂ) + (θ : ℂ) * I)‖ ^ α) := by
    intro ε hε
    refine Continuous.rpow_const (by fun_prop) (fun θ => Or.inl ?_)
    have hw : (-ε : ℂ) + (θ : ℂ) * I ∈ UcDisk := by
      rw [mem_UcDisk_iff]; simp [hε]
    exact norm_ne_zero_iff.mpr (slitPlane_ne_zero (one_sub_exp_mem_slitPlane hw))
  rcases lt_or_ge α 0 with hα_neg | hα_nonneg
  · rcases integral_add_abs_rpow_le hα with ⟨C0, hC0_nonneg, hC0⟩
    set c := Real.exp (-1 / 2) / π
    have hc_pos : 0 < c := by positivity
    refine ⟨c ^ α * C0, by positivity, fun {ε} hε_pos hε_le => ?_⟩
    have h_cont_rhs : Continuous (fun θ : ℝ => c ^ α * (ε + |θ|) ^ α) := by
      refine continuous_const.mul (Continuous.rpow_const (by fun_prop) (fun θ => Or.inl ?_))
      have : 0 < ε + |θ| := by positivity
      exact this.ne'
    have h_mono : (∫ θ in (-π / 2)..(π / 2), ‖1 - Complex.exp ((-ε : ℂ) + (θ : ℂ) * I)‖ ^ α) ≤
        ∫ θ in (-π / 2)..(π / 2), c ^ α * (ε + |θ|) ^ α := by
      refine intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
        ((h_cont_lhs hε_pos).intervalIntegrable _ _)
        (h_cont_rhs.intervalIntegrable _ _) (fun θ hθ => ?_)
      have h_ge := norm_one_sub_exp_ge_of_mem_Icc hε_pos hε_le hθ
      have h_pos : 0 < c * (ε + |θ|) := by positivity
      calc
        ‖1 - Complex.exp ((-ε : ℂ) + (θ : ℂ) * I)‖ ^ α
          ≤ (c * (ε + |θ|)) ^ α := Real.rpow_le_rpow_of_nonpos h_pos h_ge hα_neg.le
        _ = c ^ α * (ε + |θ|) ^ α := Real.mul_rpow hc_pos.le (by positivity)
    rw [intervalIntegral.integral_const_mul] at h_mono
    calc
      (∫ θ in (-π / 2)..(π / 2), ‖1 - Complex.exp ((-ε : ℂ) + (θ : ℂ) * I)‖ ^ α)
        ≤ c ^ α * ∫ θ in (-π / 2)..(π / 2), (ε + |θ|) ^ α := h_mono
      _ ≤ c ^ α * (C0 * (ε ^ (α + 1) + 1)) :=
        mul_le_mul_of_nonneg_left (hC0 hε_pos hε_le) (by positivity)
      _ = (c ^ α * C0) * (ε ^ (α + 1) + 1) := by ring
  · refine ⟨π * (2 : ℝ) ^ α, by positivity, fun {ε} hε_pos _ => ?_⟩
    have h_mono : (∫ θ in (-π / 2)..(π / 2), ‖1 - Complex.exp ((-ε : ℂ) + (θ : ℂ) * I)‖ ^ α) ≤
        ∫ _ in (-π / 2)..(π / 2), (2 : ℝ) ^ α := by
      refine intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
        ((h_cont_lhs hε_pos).intervalIntegrable _ _)
        intervalIntegrable_const (fun θ _ => ?_)
      have hexp_le1 : Real.exp (-ε) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have h_le2 : ‖1 - Complex.exp ((-ε : ℂ) + (θ : ℂ) * I)‖ ≤ 2 := by
        calc
          ‖1 - Complex.exp ((-ε : ℂ) + (θ : ℂ) * I)‖
            ≤ ‖(1 : ℂ)‖ + ‖Complex.exp ((-ε : ℂ) + (θ : ℂ) * I)‖ := norm_sub_le _ _
          _ = 1 + Real.exp (-ε) := by simp [Complex.norm_exp]
          _ ≤ 2 := by linarith
      exact Real.rpow_le_rpow (norm_nonneg _) h_le2 hα_nonneg
    rw [intervalIntegral.integral_const, smul_eq_mul] at h_mono
    have h_len : π / 2 - -π / 2 = π := by ring
    rw [h_len] at h_mono
    have h_eps_nonneg : 0 ≤ ε ^ (α + 1) := by positivity
    calc
      (∫ θ in (-π / 2)..(π / 2), ‖1 - Complex.exp ((-ε : ℂ) + (θ : ℂ) * I)‖ ^ α)
        ≤ π * (2 : ℝ) ^ α := h_mono
      _ ≤ (π * (2 : ℝ) ^ α) * (ε ^ (α + 1) + 1) := by
        nlinarith [show 0 ≤ π * (2 : ℝ) ^ α by positivity]

/-- The binomial series coefficient $\frac{(a)_n}{n!} = \binom{a + n - 1}{n}$. -/
noncomputable def pochhammerCoeff (a : ℝ) (n : ℕ) : ℝ :=
  realPochhammer a n / (Nat.factorial n : ℝ)

lemma pochhammerCoeff_nonneg {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    0 ≤ pochhammerCoeff a n := by
  dsimp [pochhammerCoeff]
  exact div_nonneg (realPochhammer_nonneg ha n) (Nat.cast_nonneg _)

lemma ringChoose_add_sub_one_eq_pochhammerCoeff (a : ℝ) (n : ℕ) :
    Ring.choose (a + (n : ℝ) - 1) n = pochhammerCoeff a n := by
  have h1 := Ring.factorial_nsmul_multichoose_eq_ascPochhammer a n
  rw [Ring.multichoose_eq, Polynomial.ascPochhammer_smeval_eq_eval, nsmul_eq_mul] at h1
  have hne : (Nat.factorial n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  exact eq_div_of_mul_eq hne (by rw [mul_comm, h1]; rfl)

/-- Real binomial series expansion of $(1 - x)^{-a}$ for $|x| < 1$. -/
lemma hasSum_one_sub_rpow_neg (a : ℝ) {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ => pochhammerCoeff a n * x ^ n) ((1 - x) ^ (-a)) := by
  have hx_eball : x ∈ Metric.eball (0 : ℝ) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa using hx
  have h_fp := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero a).hasSum hx_eball
  rw [FormalMultilinearSeries.ofScalars_apply_eq', zero_add, one_div, ← Real.rpow_neg] at h_fp
  · refine h_fp.congr_fun fun n => ?_
    rw [smul_eq_mul, ringChoose_add_sub_one_eq_pochhammerCoeff]
  · have : x < 1 := (abs_lt.mp hx).2
    linarith

/-- Complex binomial series expansion of $(1 - z)^{-a}$ for $\|z\| < 1$. -/
lemma hasSum_one_sub_cpow_neg (a : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (pochhammerCoeff a n : ℂ) * z ^ n) ((1 - z) ^ (- (a : ℂ))) := by
  have hz_eball : z ∈ Metric.eball (0 : ℂ) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa using hz
  have h_fp := (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero (a : ℂ)).hasSum hz_eball
  rw [FormalMultilinearSeries.ofScalars_apply_eq', zero_add, one_div, ← Complex.cpow_neg] at h_fp
  refine h_fp.congr_fun fun n => ?_
  rw [smul_eq_mul]
  congr 1
  have h_cast : (a : ℂ) + (n : ℂ) - 1 = ((a + (n : ℝ) - 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [h_cast, ← Complex.ofReal_choose, ringChoose_add_sub_one_eq_pochhammerCoeff]

/-- Binomial series expansion of $e^{\Delta_\phi \sigma} (1 - e^\sigma)^{-2\Delta_\phi}$ for
$\sigma < 0$. -/
lemma hasSum_exp_mul_one_sub_exp_rpow_neg (Δ_phi : ℝ) {σ : ℝ} (hσ : σ < 0) :
    HasSum
      (fun n : ℕ => pochhammerCoeff (2 * Δ_phi) n * Real.exp ((Δ_phi + (n : ℝ)) * σ))
      (Real.exp (Δ_phi * σ) * (1 - Real.exp σ) ^ (- (2 * Δ_phi))) := by
  have h_abs : |Real.exp σ| < 1 := by
    rw [abs_of_pos (Real.exp_pos σ)]
    exact Real.exp_lt_one_iff.mpr hσ
  have h_sum := (hasSum_one_sub_rpow_neg (2 * Δ_phi) h_abs).mul_left (Real.exp (Δ_phi * σ))
  refine h_sum.congr_fun fun n => ?_
  rw [← mul_left_comm, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 2
  ring

/-- Binomial series expansion of $e^{\Delta_\phi w} (1 - e^w)^{-2\Delta_\phi}$ on
$w \in \operatorname{UcDisk}$. -/
lemma hasSum_exp_mul_one_sub_exp_cpow_neg (Δ_phi : ℝ) {w : ℂ} (hw : w ∈ UcDisk) :
    HasSum
      (fun n : ℕ =>
        (pochhammerCoeff (2 * Δ_phi) n : ℂ) *
          Complex.exp (((Δ_phi + (n : ℝ) : ℝ) : ℂ) * w))
      (Complex.exp ((Δ_phi : ℂ) * w) * (1 - Complex.exp w) ^ (- (2 * Δ_phi : ℂ))) := by
  have h_sum :=
    (hasSum_one_sub_cpow_neg (2 * Δ_phi) (exp_norm_lt_one_of_mem_UcDisk hw)).mul_left
      (Complex.exp ((Δ_phi : ℂ) * w))
  rw [Complex.ofReal_mul, Complex.ofReal_ofNat] at h_sum
  refine h_sum.congr_fun fun n => ?_
  rw [← mul_left_comm, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 2
  push_cast
  ring

lemma universalLaplace_eq (Δ_phi : ℝ) (w : ℂ) :
    universalLaplace Δ_phi w =
      ((2 * (4 : ℝ) ^ (2 * Δ_phi) / Real.Gamma (2 * Δ_phi) : ℝ) : ℂ) *
        (Complex.exp ((Δ_phi : ℂ) * w) * (1 - Complex.exp w) ^ (- (2 * Δ_phi : ℂ))) := by
  dsimp [universalLaplace, crossFactor]
  have h4_cast : (4 : ℂ) ^ (Δ_phi : ℂ) = (((4 : ℝ) ^ Δ_phi : ℝ) : ℂ) := by
    have : (4 : ℂ) = ((4 : ℝ) : ℂ) := by norm_cast
    rw [this, ← Complex.ofReal_cpow (by norm_num)]
  have h4_sq : (4 : ℝ) ^ (2 * Δ_phi) = (4 : ℝ) ^ Δ_phi * (4 : ℝ) ^ Δ_phi := by
    rw [← Real.rpow_add (by norm_num), two_mul]
  rw [h4_cast, h4_sq]
  push_cast
  ring

/-- Integrating `universalLaplace Δ_phi (σ + i t)` against `laplaceFourierTransform φ σ t` along any
vertical line $\sigma < 0$ expands the binomial series of $(1 - e^w)^{-2\Delta_\phi}$ and recovers
`universalMonomialPairing Δ_phi φ`. -/
theorem integral_laplaceFourierTransform_mul_universalLaplace
    {Δ_phi : ℝ} (hΔ : 0 < Δ_phi)
    {φ : ℝ → ℝ} (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_supp : HasCompactSupport φ)
    {σ : ℝ} (hσ : σ < 0) :
    (2 * π : ℂ)⁻¹ * (∫ t : ℝ,
      laplaceFourierTransform φ σ t * universalLaplace Δ_phi ((σ : ℂ) + (t : ℂ) * I)) =
      (universalMonomialPairing Δ_phi φ : ℂ) := by
  set c : ℝ := 2 * (4 : ℝ) ^ (2 * Δ_phi) / Real.Gamma (2 * Δ_phi)
  set F : ℕ → ℝ → ℂ := fun n t =>
    (pochhammerCoeff (2 * Δ_phi) n : ℂ) *
      (laplaceFourierTransform φ σ t *
        Complex.exp (((Δ_phi + (n : ℝ) : ℝ) : ℂ) * ((σ : ℂ) + (t : ℂ) * I)))
  set bound : ℕ → ℝ → ℝ := fun n t =>
    (pochhammerCoeff (2 * Δ_phi) n * Real.exp ((Δ_phi + (n : ℝ)) * σ)) *
      ‖laplaceFourierTransform φ σ t‖
  have h_mem : ∀ t : ℝ, (σ : ℂ) + (t : ℂ) * I ∈ UcDisk := by
    intro t
    change ((σ : ℂ) + (t : ℂ) * I).re < 0
    simpa using hσ
  have h_sum_real := hasSum_exp_mul_one_sub_exp_rpow_neg Δ_phi hσ
  have h_hasSum_int :
      HasSum (fun n : ℕ => ∫ t : ℝ, F n t)
        (∫ t : ℝ, laplaceFourierTransform φ σ t *
          (Complex.exp ((Δ_phi : ℂ) * ((σ : ℂ) + (t : ℂ) * I)) *
            (1 - Complex.exp ((σ : ℂ) + (t : ℂ) * I)) ^ (- (2 * Δ_phi : ℂ)))) := by
    refine hasSum_integral_of_dominated_convergence bound ?_ ?_ ?_ ?_ ?_
    · intro n
      have h1 := continuous_laplaceFourierTransform hφ_smooth.continuous hφ_supp σ
      have h2 : Continuous (fun t : ℝ =>
          Complex.exp (((Δ_phi + (n : ℝ) : ℝ) : ℂ) * ((σ : ℂ) + (t : ℂ) * I))) := by fun_prop
      exact (continuous_const.mul (h1.mul h2)).aestronglyMeasurable
    · intro n
      filter_upwards with t
      dsimp [F, bound]
      rw [norm_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (pochhammerCoeff_nonneg (by positivity) n), Complex.norm_exp]
      have h_re : (((Δ_phi + (n : ℝ) : ℝ) : ℂ) * ((σ : ℂ) + (t : ℂ) * I)).re =
          (Δ_phi + (n : ℝ)) * σ := by
        simp [Complex.mul_re]
      rw [h_re]
      ring_nf
      exact le_rfl
    · filter_upwards with t
      exact h_sum_real.summable.mul_right ‖laplaceFourierTransform φ σ t‖
    · have h_tsum : (fun t : ℝ => ∑' n : ℕ, bound n t) =
          fun t : ℝ => (Real.exp (Δ_phi * σ) * (1 - Real.exp σ) ^ (- (2 * Δ_phi))) *
            ‖laplaceFourierTransform φ σ t‖ := by
        ext t
        exact (h_sum_real.mul_right ‖laplaceFourierTransform φ σ t‖).tsum_eq
      rw [h_tsum]
      exact (integrable_laplaceFourierTransform hφ_smooth hφ_supp σ).norm.const_mul _
    · filter_upwards with t
      have h_pt := (hasSum_exp_mul_one_sub_exp_cpow_neg Δ_phi (h_mem t)).mul_left
        (laplaceFourierTransform φ σ t)
      refine h_pt.congr_fun fun n => ?_
      dsimp [F]
      ring
  have h_term : ∀ n : ℕ,
      (2 * π : ℂ)⁻¹ * (∫ t : ℝ, F n t) =
        (((pochhammerCoeff (2 * Δ_phi) n * φ (Δ_phi + (n : ℝ)) : ℝ) : ℂ)) := by
    intro n
    dsimp [F]
    rw [integral_const_mul, ← mul_assoc, mul_comm (2 * π : ℂ)⁻¹, mul_assoc,
      MonomialFourPointData.integral_laplaceFourierTransform_mul_exp hφ_smooth hφ_supp σ
        (Δ_phi + (n : ℝ))]
    push_cast
    rfl
  have h_hasSum_scaled := h_hasSum_int.mul_left (2 * π : ℂ)⁻¹
  simp_rw [h_term] at h_hasSum_scaled
  have h_tsum_eq := h_hasSum_scaled.tsum_eq
  have h_int_rewrite :
      (∫ t : ℝ, laplaceFourierTransform φ σ t * universalLaplace Δ_phi ((σ : ℂ) + (t : ℂ) * I)) =
        (c : ℂ) * ∫ t : ℝ, laplaceFourierTransform φ σ t *
          (Complex.exp ((Δ_phi : ℂ) * ((σ : ℂ) + (t : ℂ) * I)) *
            (1 - Complex.exp ((σ : ℂ) + (t : ℂ) * I)) ^ (- (2 * Δ_phi : ℂ))) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    dsimp only
    rw [universalLaplace_eq]
    dsimp [c]
    ring
  rw [h_int_rewrite, ← mul_assoc, mul_comm (2 * π : ℂ)⁻¹, mul_assoc, ← h_tsum_eq]
  dsimp [universalMonomialPairing, c, pochhammerCoeff]
  rw [Complex.ofReal_mul, Complex.ofReal_tsum]

/-!
## Large-Spin Asymptotics of the $t$-Channel Identity Projection `identityProjSpin`
-/

@[simp]
lemma pochhammerCoeff_zero (a : ℝ) : pochhammerCoeff a 0 = 1 := by
  simp [pochhammerCoeff]

lemma pochhammerCoeff_succ (a : ℝ) (n : ℕ) :
    pochhammerCoeff a (n + 1) = pochhammerCoeff a n * ((a + (n : ℝ)) / ((n : ℝ) + 1)) := by
  dsimp [pochhammerCoeff]
  rw [realPochhammer_succ, Nat.factorial_succ]
  push_cast
  rw [div_mul_div_comm, mul_comm ((n : ℝ) + 1)]

/-- Uniform submultiplicative bound on shifted binomial coefficients:
for $a \ge 0$ and all $K, n \in \mathbb{N}$,
$$\frac{(a)_{n + K}}{(n + K)!} \le \frac{(a)_K}{K!} \frac{(a + 1)_n}{n!}.$$ -/
lemma pochhammerCoeff_add_le {a : ℝ} (ha : 0 ≤ a) (K n : ℕ) :
    pochhammerCoeff a (n + K) ≤ pochhammerCoeff a K * pochhammerCoeff (a + 1) n := by
  induction n with
  | zero => simp
  | succ m ih =>
    have h_add : m + 1 + K = (m + K) + 1 := by omega
    rw [h_add, pochhammerCoeff_succ, pochhammerCoeff_succ, ← mul_assoc]
    refine mul_le_mul ih ?_ (by positivity)
      (mul_nonneg (pochhammerCoeff_nonneg ha K) (pochhammerCoeff_nonneg (by linarith) m))
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    nlinarith [ha, (Nat.cast_nonneg m : (0 : ℝ) ≤ m), (Nat.cast_nonneg K : (0 : ℝ) ≤ K)]

lemma prod_range_add_eq_realPochhammer (a : ℝ) (n : ℕ) :
    (∏ j ∈ Finset.range n, (a + (j : ℝ))) = realPochhammer a n := by
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.prod_range_succ, ih, realPochhammer_succ]

/-- Euler's Gamma limit for binomial coefficients: for $a > 0$,
$$\lim_{M \to \infty} M^{1 - a} \frac{(a)_M}{M!} = \frac{1}{\Gamma(a)}.$$ -/
lemma tendsto_rpow_mul_pochhammerCoeff {a : ℝ} (ha : 0 < a) :
    Tendsto (fun M : ℕ => (M : ℝ) ^ (1 - a) * pochhammerCoeff a M)
      atTop (𝓝 (Real.Gamma a)⁻¹) := by
  have h_gamma := (Real.GammaSeq_tendsto_Gamma a).inv₀ (Real.Gamma_pos_of_pos ha).ne'
  have h_rat : Tendsto (fun M : ℕ => (1 + a / (M : ℝ))⁻¹) atTop (𝓝 1⁻¹) := by
    have h1 : Tendsto (fun M : ℕ => 1 + a / (M : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add
        (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ)))
    rw [add_zero] at h1
    exact h1.inv₀ one_ne_zero
  have h_prod := h_gamma.mul h_rat
  rw [inv_one, mul_one] at h_prod
  refine h_prod.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with M hM
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hM_ne : (M : ℝ) ≠ 0 := hM_pos.ne'
  have h_poch_pos : 0 < realPochhammer a M := realPochhammer_pos ha M
  have h_poch_ne : realPochhammer a M ≠ 0 := h_poch_pos.ne'
  have h_aM_pos : 0 < a + (M : ℝ) := by positivity
  have h_aM_ne : a + (M : ℝ) ≠ 0 := h_aM_pos.ne'
  have h_fact_ne : (M.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero M)
  have h_Ma_pos : 0 < (M : ℝ) ^ a := Real.rpow_pos_of_pos hM_pos a
  have h_Ma_ne : (M : ℝ) ^ a ≠ 0 := h_Ma_pos.ne'
  dsimp [Real.GammaSeq, pochhammerCoeff]
  rw [prod_range_add_eq_realPochhammer a (M + 1), realPochhammer_succ]
  have h_rpow : (M : ℝ) ^ (1 - a) * (M : ℝ) ^ a = (M : ℝ) := by
    rw [← Real.rpow_add hM_pos, sub_add_cancel, Real.rpow_one]
  have h_one_add : (1 + a / (M : ℝ))⁻¹ = (M : ℝ) / (a + (M : ℝ)) := by
    have : 1 + a / (M : ℝ) = (a + (M : ℝ)) / (M : ℝ) := by field_simp; ring
    rw [this, inv_div]
  rw [h_one_add, inv_div]
  apply mul_right_cancel₀ h_Ma_ne
  calc
    (realPochhammer a M * (a + (M : ℝ)) / ((M : ℝ) ^ a * (M.factorial : ℝ)) *
        ((M : ℝ) / (a + (M : ℝ)))) * (M : ℝ) ^ a
      = realPochhammer a M / (M.factorial : ℝ) * (M : ℝ) := by
        field_simp
    _ = (M : ℝ) ^ (1 - a) * (realPochhammer a M / (M.factorial : ℝ)) * (M : ℝ) ^ a := by
        rw [mul_right_comm, h_rpow, mul_comm]

/-- Shifted Euler Gamma limit: for $a > 0$ and any fixed $n \in \mathbb{N}$,
$$\lim_{K \to \infty} K^{1 - a} \frac{(a)_{n + K}}{(n + K)!} = \frac{1}{\Gamma(a)}.$$ -/
lemma tendsto_rpow_mul_pochhammerCoeff_add {a : ℝ} (ha : 0 < a) (n : ℕ) :
    Tendsto (fun K : ℕ => (K : ℝ) ^ (1 - a) * pochhammerCoeff a (n + K))
      atTop (𝓝 (Real.Gamma a)⁻¹) := by
  have h_shift : Tendsto
      (fun K : ℕ => ((n + K : ℕ) : ℝ) ^ (1 - a) * pochhammerCoeff a (n + K))
      atTop (𝓝 (Real.Gamma a)⁻¹) := by
    have h_comp := (tendsto_rpow_mul_pochhammerCoeff ha).comp (tendsto_add_atTop_nat n)
    refine h_comp.congr fun K => ?_
    dsimp [Function.comp_def]
    rw [add_comm K n]
  have h_ratio : Tendsto (fun K : ℕ => (1 + (n : ℝ) / (K : ℝ)) ^ (a - 1)) atTop (𝓝 1) := by
    have h1 : Tendsto (fun K : ℕ => 1 + (n : ℝ) / (K : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add
        (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ)))
    rw [add_zero] at h1
    simpa using h1.rpow tendsto_const_nhds (Or.inl one_ne_zero)
  have h_prod := h_shift.mul h_ratio
  rw [mul_one] at h_prod
  refine h_prod.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with K hK
  have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have h_pos : 0 < 1 + (n : ℝ) / (K : ℝ) := by positivity
  have h_cast : ((n + K : ℕ) : ℝ) = (K : ℝ) * (1 + (n : ℝ) / (K : ℝ)) := by
    push_cast; field_simp; ring
  rw [h_cast, Real.mul_rpow hK_pos.le h_pos.le]
  have h_cancel :
      (1 + (n : ℝ) / (K : ℝ)) ^ (1 - a) * (1 + (n : ℝ) / (K : ℝ)) ^ (a - 1) = 1 := by
    rw [← Real.rpow_add h_pos, sub_add_sub_cancel, sub_self, Real.rpow_zero]
  calc
    (K : ℝ) ^ (1 - a) * (1 + (n : ℝ) / (K : ℝ)) ^ (1 - a) * pochhammerCoeff a (n + K) *
        (1 + (n : ℝ) / (K : ℝ)) ^ (a - 1)
      = (K : ℝ) ^ (1 - a) * pochhammerCoeff a (n + K) *
          ((1 + (n : ℝ) / (K : ℝ)) ^ (1 - a) * (1 + (n : ℝ) / (K : ℝ)) ^ (a - 1)) := by ring
    _ = (K : ℝ) ^ (1 - a) * pochhammerCoeff a (n + K) := by rw [h_cancel, mul_one]

/-- Tannery's theorem applied to the binomial series of `identityProjSpinFull`: for $a > 0$ and
$\sigma < 0$,
$$\lim_{K \to \infty} K^{1 - a} \sum_{n=0}^{\infty}
  \frac{(a)_n}{n!} \frac{(a)_{n + K}}{(n + K)!} e^{n \sigma}
  = \frac{1}{\Gamma(a)} (1 - e^\sigma)^{-a}.$$ -/
lemma tendsto_rpow_mul_tsum_pochhammerCoeff {a : ℝ} (ha : 0 < a) {σ : ℝ} (hσ : σ < 0) :
    Tendsto
      (fun K : ℕ =>
        (K : ℝ) ^ (1 - a) *
          ∑' n : ℕ, pochhammerCoeff a n * pochhammerCoeff a (n + K) * (Real.exp σ) ^ n)
      atTop (𝓝 ((Real.Gamma a)⁻¹ * (1 - Real.exp σ) ^ (-a))) := by
  set q := Real.exp (σ / 2)
  have hq_pos : 0 < q := Real.exp_pos _
  have hq_lt1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hq_abs : |q| < 1 := by rw [abs_of_pos hq_pos]; exact hq_lt1
  have h_exp_abs : |Real.exp σ| < 1 := by
    rw [abs_of_pos (Real.exp_pos σ)]; exact Real.exp_lt_one_iff.mpr hσ
  have h_sum_a := hasSum_one_sub_rpow_neg a hq_abs
  have h_sum_a1 := hasSum_one_sub_rpow_neg (a + 1) hq_abs
  have h_sum_σ := hasSum_one_sub_rpow_neg a h_exp_abs
  set C_a := (Real.Gamma a)⁻¹ + 1
  have hCa_pos : 0 < C_a := by
    dsimp [C_a]
    have := Real.Gamma_pos_of_pos ha
    positivity
  set S_a := (1 - q) ^ (-a)
  let f : ℕ → ℕ → ℝ := fun K n =>
    ((K : ℝ) ^ (1 - a) * pochhammerCoeff a (n + K)) *
      (pochhammerCoeff a n * (Real.exp σ) ^ n)
  let g : ℕ → ℝ := fun n =>
    (Real.Gamma a)⁻¹ * (pochhammerCoeff a n * (Real.exp σ) ^ n)
  let bound : ℕ → ℝ := fun n =>
    (C_a * S_a) * (pochhammerCoeff (a + 1) n * q ^ n)
  have h_tannery : Tendsto (fun K : ℕ => ∑' n : ℕ, f K n) atTop (𝓝 (∑' n : ℕ, g n)) := by
    refine tendsto_tsum_of_dominated_convergence (h_sum_a1.summable.mul_left (C_a * S_a))
      (fun n => (tendsto_rpow_mul_pochhammerCoeff_add ha n).mul_const _) ?_
    have h_ev : ∀ᶠ K : ℕ in atTop, (K : ℝ) ^ (1 - a) * pochhammerCoeff a K < C_a :=
      (tendsto_rpow_mul_pochhammerCoeff ha).eventually (gt_mem_nhds (by dsimp [C_a]; linarith))
    filter_upwards [h_ev] with K hK n
    have h_nonneg : 0 ≤ f K n := by
      dsimp [f]
      exact mul_nonneg (mul_nonneg (by positivity) (pochhammerCoeff_nonneg ha.le _))
        (mul_nonneg (pochhammerCoeff_nonneg ha.le _) (by positivity))
    rw [Real.norm_of_nonneg h_nonneg]
    have h_step1 : (K : ℝ) ^ (1 - a) * pochhammerCoeff a (n + K) ≤
        C_a * pochhammerCoeff (a + 1) n := by
      calc
        (K : ℝ) ^ (1 - a) * pochhammerCoeff a (n + K)
          ≤ (K : ℝ) ^ (1 - a) * (pochhammerCoeff a K * pochhammerCoeff (a + 1) n) :=
            mul_le_mul_of_nonneg_left (pochhammerCoeff_add_le ha.le K n) (by positivity)
        _ = ((K : ℝ) ^ (1 - a) * pochhammerCoeff a K) * pochhammerCoeff (a + 1) n := by ring
        _ ≤ C_a * pochhammerCoeff (a + 1) n :=
          mul_le_mul_of_nonneg_right hK.le (pochhammerCoeff_nonneg (by linarith) n)
    have h_step2 : pochhammerCoeff a n * q ^ n ≤ S_a := by
      rw [← h_sum_a.tsum_eq]
      exact h_sum_a.summable.le_tsum n
        (fun m _ => mul_nonneg (pochhammerCoeff_nonneg ha.le m) (by positivity))
    have h_q_sq : (Real.exp σ) ^ n = q ^ n * q ^ n := by
      rw [← mul_pow, ← Real.exp_add, add_halves]
    dsimp [f, bound]
    rw [h_q_sq]
    calc
      ((K : ℝ) ^ (1 - a) * pochhammerCoeff a (n + K)) *
          (pochhammerCoeff a n * (q ^ n * q ^ n))
        = ((K : ℝ) ^ (1 - a) * pochhammerCoeff a (n + K)) *
            ((pochhammerCoeff a n * q ^ n) * q ^ n) := by ring
      _ ≤ (C_a * pochhammerCoeff (a + 1) n) * (S_a * q ^ n) := by
        refine mul_le_mul h_step1
          (mul_le_mul_of_nonneg_right h_step2 (by positivity))
          (mul_nonneg (mul_nonneg (pochhammerCoeff_nonneg ha.le n) (by positivity)) (by positivity))
          (mul_nonneg hCa_pos.le (pochhammerCoeff_nonneg (by linarith) n))
      _ = C_a * S_a * (pochhammerCoeff (a + 1) n * q ^ n) := by ring
  have h_g_tsum : (∑' n : ℕ, g n) = (Real.Gamma a)⁻¹ * (1 - Real.exp σ) ^ (-a) :=
    (h_sum_σ.mul_left (Real.Gamma a)⁻¹).tsum_eq
  rw [h_g_tsum] at h_tannery
  refine h_tannery.congr fun K => ?_
  dsimp [f]
  rw [← tsum_mul_left]
  congr 1
  ext n
  ring

/-- The full $[-\pi, \pi]$ $\theta$-integral of the $t$-channel identity contribution
`crossIdentity Δ_phi`:
$$\int_{-\pi}^{\pi} \frac{d\theta}{\pi} \,
  e^{-J (w_r + i\theta)} \, \mathcal{G}_{\text{id}}(w_l - i\theta, w_r + i\theta).$$ -/
noncomputable def identityProjSpinFull (Δ_phi : ℝ) (J : ℤ) (wl wr : ℂ) : ℂ :=
  (π : ℂ)⁻¹ * ∫ θ in (-π)..π,
    Complex.exp (- (J : ℂ) * (wr + (θ : ℂ) * I)) *
      crossIdentity Δ_phi (wl - (θ : ℂ) * I) (wr + (θ : ℂ) * I)

/-- Binomial series expansion of `crossFactor Δ_phi w` on `w ∈ UcDisk`. -/
lemma hasSum_crossFactor (Δ_phi : ℝ) {w : ℂ} (hw : w ∈ UcDisk) :
    HasSum
      (fun n : ℕ =>
        (((4 : ℝ) ^ Δ_phi * pochhammerCoeff (2 * Δ_phi) n : ℝ) : ℂ) *
          Complex.exp (((Δ_phi + (n : ℝ) : ℝ) : ℂ) * w))
      (crossFactor Δ_phi w) := by
  have h_sum :=
    (hasSum_exp_mul_one_sub_exp_cpow_neg Δ_phi hw).mul_left (((4 : ℝ) ^ Δ_phi : ℝ) : ℂ)
  have h_cf : (((4 : ℝ) ^ Δ_phi : ℝ) : ℂ) *
      (Complex.exp ((Δ_phi : ℂ) * w) * (1 - Complex.exp w) ^ (- (2 * Δ_phi : ℂ))) =
      crossFactor Δ_phi w := by
    dsimp [crossFactor]
    have h4_cast : (4 : ℂ) ^ (Δ_phi : ℂ) = (((4 : ℝ) ^ Δ_phi : ℝ) : ℂ) := by
      have : (4 : ℂ) = ((4 : ℝ) : ℂ) := by norm_cast
      rw [this, ← Complex.ofReal_cpow (by norm_num)]
    rw [h4_cast]
    ring
  rw [h_cf] at h_sum
  refine h_sum.congr_fun fun n => ?_
  push_cast
  ring

/-- Fourier coefficient extraction from `crossFactor Δ_phi (wr + i θ)` on $[-\pi, \pi]$:
for $\Delta_\phi > 0$, $M \in \mathbb{N}$, and $w_r \in \operatorname{UcDisk}$,
$$\int_{-\pi}^{\pi} e^{-i(\Delta_\phi + M)\theta}
  \operatorname{crossFactor}(\Delta_\phi, w_r + i\theta) \, d\theta
  = 2\pi \cdot 4^{\Delta_\phi} \frac{(2\Delta_\phi)_M}{M!} \, e^{(\Delta_\phi + M) w_r}.$$ -/
lemma integral_exp_mul_crossFactor_shift {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) (M : ℕ)
    {wr : ℂ} (hwr : wr ∈ UcDisk) :
    (∫ θ in (-π)..π,
      Complex.exp (- ((Δ_phi + (M : ℝ) : ℝ) : ℂ) * (θ : ℂ) * I) *
        crossFactor Δ_phi (wr + (θ : ℂ) * I)) =
      (2 * π : ℂ) * (((4 : ℝ) ^ Δ_phi * pochhammerCoeff (2 * Δ_phi) M : ℝ) : ℂ) *
        Complex.exp (((Δ_phi + (M : ℝ) : ℝ) : ℂ) * wr) := by
  set F : ℕ → ℝ → ℂ := fun m θ =>
    ((((4 : ℝ) ^ Δ_phi * pochhammerCoeff (2 * Δ_phi) m : ℝ) : ℂ) *
      Complex.exp (((Δ_phi + (m : ℝ) : ℝ) : ℂ) * wr)) *
      Complex.exp ((((m : ℤ) - (M : ℤ) : ℤ) : ℂ) * (θ : ℂ) * I)
  set bound : ℕ → ℝ → ℝ := fun m _ =>
    (4 : ℝ) ^ Δ_phi *
      (pochhammerCoeff (2 * Δ_phi) m * Real.exp ((Δ_phi + (m : ℝ)) * wr.re))
  have h_sum_real := (hasSum_exp_mul_one_sub_exp_rpow_neg Δ_phi hwr).mul_left ((4 : ℝ) ^ Δ_phi)
  have h_hasSum_int :
      HasSum (fun m : ℕ => ∫ θ in (-π)..π, F m θ)
        (∫ θ in (-π)..π,
          Complex.exp (- ((Δ_phi + (M : ℝ) : ℝ) : ℂ) * (θ : ℂ) * I) *
            crossFactor Δ_phi (wr + (θ : ℂ) * I)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
      bound ?_ ?_ ?_ ?_ ?_
    · intro m
      have h_cont : Continuous (F m) := by dsimp [F]; fun_prop
      exact h_cont.aestronglyMeasurable
    · intro m
      filter_upwards with θ _
      dsimp [F, bound]
      rw [norm_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (mul_nonneg (by positivity) (pochhammerCoeff_nonneg (by positivity) m)),
        Complex.norm_exp, Complex.norm_exp]
      have h_re1 : (((Δ_phi + (m : ℝ) : ℝ) : ℂ) * wr).re = (Δ_phi + (m : ℝ)) * wr.re := by
        simp [Complex.mul_re]
      have h_re2 : ((((m : ℤ) - (M : ℤ) : ℤ) : ℂ) * (θ : ℂ) * I).re = 0 := by
        simp [Complex.mul_re]
      rw [h_re1, h_re2, Real.exp_zero, mul_one, mul_assoc]
    · filter_upwards with θ _
      exact h_sum_real.summable
    · exact intervalIntegrable_const (c := ∑' m : ℕ,
        (4 : ℝ) ^ Δ_phi *
          (pochhammerCoeff (2 * Δ_phi) m * Real.exp ((Δ_phi + (m : ℝ)) * wr.re)))
    · filter_upwards with θ _
      have hwr_θ : wr + (θ : ℂ) * I ∈ UcDisk :=
        MonomialFourPointData.add_I_mul_mem_UcDisk hwr θ
      have h_pt := (hasSum_crossFactor Δ_phi hwr_θ).mul_left
        (Complex.exp (- ((Δ_phi + (M : ℝ) : ℝ) : ℂ) * (θ : ℂ) * I))
      refine h_pt.congr_fun fun m => ?_
      dsimp [F]
      have h_exp :
          Complex.exp (- ((Δ_phi + (M : ℝ) : ℝ) : ℂ) * (θ : ℂ) * I) *
            Complex.exp (((Δ_phi + (m : ℝ) : ℝ) : ℂ) * (wr + (θ : ℂ) * I)) =
          Complex.exp (((Δ_phi + (m : ℝ) : ℝ) : ℂ) * wr) *
            Complex.exp ((((m : ℤ) - (M : ℤ) : ℤ) : ℂ) * (θ : ℂ) * I) := by
        rw [← Complex.exp_add, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      linear_combination
        -(((4 : ℝ) ^ Δ_phi * pochhammerCoeff (2 * Δ_phi) m : ℝ) : ℂ) * h_exp
  have h_term : ∀ m : ℕ,
      (∫ θ in (-π)..π, F m θ) =
        if m = M then
          (2 * π : ℂ) * (((4 : ℝ) ^ Δ_phi * pochhammerCoeff (2 * Δ_phi) M : ℝ) : ℂ) *
            Complex.exp (((Δ_phi + (M : ℝ) : ℝ) : ℂ) * wr)
        else 0 := by
    intro m
    dsimp [F]
    rw [intervalIntegral.integral_const_mul,
      integral_exp_int_mul_I ((m : ℤ) - (M : ℤ))]
    simp only [sub_eq_zero, Int.ofNat_inj]
    split_ifs with hm
    · subst hm
      ring
    · ring
  simp_rw [h_term] at h_hasSum_int
  exact h_hasSum_int.unique
    (hasSum_ite_eq M
      ((2 * π : ℂ) * (((4 : ℝ) ^ Δ_phi * pochhammerCoeff (2 * Δ_phi) M : ℝ) : ℂ) *
        Complex.exp (((Δ_phi + (M : ℝ) : ℝ) : ℂ) * wr)))

/-- Exact binomial series evaluation of `identityProjSpinFull` on $[-\pi, \pi]$ for
$K \in \mathbb{N}$ and $w_l, w_r \in \operatorname{UcDisk}$:
$$\operatorname{identityProjSpinFull}(\Delta_\phi, K, w_l, w_r)
  = 2 \cdot 4^{2\Delta_\phi} e^{\Delta_\phi(w_l + w_r)} \sum_{n=0}^{\infty}
    \frac{(2\Delta_\phi)_n}{n!} \frac{(2\Delta_\phi)_{n + K}}{(n + K)!} e^{n(w_l + w_r)}.$$ -/
lemma hasSum_identityProjSpinFull {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) (K : ℕ) {wl wr : ℂ}
    (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) :
    HasSum
      (fun n : ℕ =>
        (((2 * (4 : ℝ) ^ (2 * Δ_phi)) *
          pochhammerCoeff (2 * Δ_phi) n * pochhammerCoeff (2 * Δ_phi) (n + K) : ℝ) : ℂ) *
          Complex.exp (((Δ_phi + (n : ℝ) : ℝ) : ℂ) * (wl + wr)))
      (identityProjSpinFull Δ_phi (K : ℤ) wl wr) := by
  set F : ℕ → ℝ → ℂ := fun n θ =>
    ((((4 : ℝ) ^ Δ_phi * pochhammerCoeff (2 * Δ_phi) n : ℝ) : ℂ) *
      Complex.exp (((Δ_phi + (n : ℝ) : ℝ) : ℂ) * wl - (K : ℂ) * wr)) *
      (Complex.exp (- ((Δ_phi + ((n + K : ℕ) : ℝ) : ℝ) : ℂ) * (θ : ℂ) * I) *
        crossFactor Δ_phi (wr + (θ : ℂ) * I))
  set K_wr : ℝ := (4 : ℝ) ^ Δ_phi * (1 - Real.exp wr.re) ^ (-2 * Δ_phi)
  set bound : ℕ → ℝ → ℝ := fun n _ =>
    ((4 : ℝ) ^ Δ_phi * Real.exp (- (K : ℝ) * wr.re) * K_wr) *
      (pochhammerCoeff (2 * Δ_phi) n * Real.exp ((Δ_phi + (n : ℝ)) * wl.re))
  have h_sum_wl := hasSum_exp_mul_one_sub_exp_rpow_neg Δ_phi hwl
  have h_hasSum_int :
      HasSum (fun n : ℕ => ∫ θ in (-π)..π, F n θ)
        (∫ θ in (-π)..π,
          Complex.exp (- ((K : ℤ) : ℂ) * (wr + (θ : ℂ) * I)) *
            crossIdentity Δ_phi (wl - (θ : ℂ) * I) (wr + (θ : ℂ) * I)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
      bound ?_ ?_ ?_ ?_ ?_
    · intro n
      have h_cf : Continuous (fun θ : ℝ => crossFactor Δ_phi (wr + (θ : ℂ) * I)) :=
        (continuousOn_crossFactor Δ_phi).comp_continuous (by fun_prop)
          (fun θ => MonomialFourPointData.add_I_mul_mem_UcDisk hwr θ)
      have h_cont : Continuous (F n) := by
        dsimp [F]
        exact continuous_const.mul ((by fun_prop : Continuous _).mul h_cf)
      exact h_cont.aestronglyMeasurable
    · intro n
      filter_upwards with θ _
      dsimp [F, bound]
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (mul_nonneg (by positivity) (pochhammerCoeff_nonneg (by positivity) n)),
        Complex.norm_exp, Complex.norm_exp]
      have h_re1 : (((Δ_phi + (n : ℝ) : ℝ) : ℂ) * wl - (K : ℂ) * wr).re =
          (Δ_phi + (n : ℝ)) * wl.re + (- (K : ℝ) * wr.re) := by
        simp [Complex.sub_re, Complex.mul_re]
        ring
      have h_re2 : (- ((Δ_phi + ((n + K : ℕ) : ℝ) : ℝ) : ℂ) * (θ : ℂ) * I).re = 0 := by
        simp [Complex.mul_re]
      rw [h_re1, Real.exp_add, h_re2, Real.exp_zero, one_mul]
      have hwr_θ : wr + (θ : ℂ) * I ∈ UcDisk :=
        MonomialFourPointData.add_I_mul_mem_UcDisk hwr θ
      have h_cf_le : ‖crossFactor Δ_phi (wr + (θ : ℂ) * I)‖ ≤ K_wr :=
        norm_crossFactor_le_of_re_le hΔ hwr hwr_θ (by simp)
      calc
        (4 : ℝ) ^ Δ_phi * pochhammerCoeff (2 * Δ_phi) n *
            (Real.exp ((Δ_phi + (n : ℝ)) * wl.re) * Real.exp (- (K : ℝ) * wr.re)) *
            ‖crossFactor Δ_phi (wr + (θ : ℂ) * I)‖
          ≤ (4 : ℝ) ^ Δ_phi * pochhammerCoeff (2 * Δ_phi) n *
              (Real.exp ((Δ_phi + (n : ℝ)) * wl.re) * Real.exp (- (K : ℝ) * wr.re)) * K_wr := by
            refine mul_le_mul_of_nonneg_left h_cf_le ?_
            exact mul_nonneg
              (mul_nonneg (by positivity) (pochhammerCoeff_nonneg (by positivity) n))
              (by positivity)
        _ = (4 : ℝ) ^ Δ_phi * Real.exp (- (K : ℝ) * wr.re) * K_wr *
              (pochhammerCoeff (2 * Δ_phi) n * Real.exp ((Δ_phi + (n : ℝ)) * wl.re)) := by ring
    · filter_upwards with θ _
      exact h_sum_wl.summable.mul_left _
    · exact intervalIntegrable_const (c := ∑' n : ℕ,
        ((4 : ℝ) ^ Δ_phi * Real.exp (- (K : ℝ) * wr.re) * K_wr) *
          (pochhammerCoeff (2 * Δ_phi) n * Real.exp ((Δ_phi + (n : ℝ)) * wl.re)))
    · filter_upwards with θ _
      have hwl_θ : wl - (θ : ℂ) * I ∈ UcDisk :=
        MonomialFourPointData.sub_I_mul_mem_UcDisk hwl θ
      have h_pt :=
        ((hasSum_crossFactor Δ_phi hwl_θ).mul_left
          (Complex.exp (- ((K : ℤ) : ℂ) * (wr + (θ : ℂ) * I)))).mul_right
          (crossFactor Δ_phi (wr + (θ : ℂ) * I))
      have h_ci :
          Complex.exp (- ((K : ℤ) : ℂ) * (wr + (θ : ℂ) * I)) *
            crossFactor Δ_phi (wl - (θ : ℂ) * I) *
            crossFactor Δ_phi (wr + (θ : ℂ) * I) =
          Complex.exp (- ((K : ℤ) : ℂ) * (wr + (θ : ℂ) * I)) *
            crossIdentity Δ_phi (wl - (θ : ℂ) * I) (wr + (θ : ℂ) * I) := by
        dsimp [crossIdentity]; ring
      rw [h_ci] at h_pt
      refine h_pt.congr_fun fun n => ?_
      dsimp [F]
      have h_exp :
          Complex.exp (- ((K : ℤ) : ℂ) * (wr + (θ : ℂ) * I)) *
            Complex.exp (((Δ_phi + (n : ℝ) : ℝ) : ℂ) * (wl - (θ : ℂ) * I)) =
          Complex.exp (((Δ_phi + (n : ℝ) : ℝ) : ℂ) * wl - (K : ℂ) * wr) *
            Complex.exp (- ((Δ_phi + ((n + K : ℕ) : ℝ) : ℝ) : ℂ) * (θ : ℂ) * I) := by
        rw [← Complex.exp_add, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      linear_combination
        -((((4 : ℝ) ^ Δ_phi * pochhammerCoeff (2 * Δ_phi) n : ℝ) : ℂ) *
          crossFactor Δ_phi (wr + (θ : ℂ) * I)) * h_exp
  have h_scaled := h_hasSum_int.mul_left (π : ℂ)⁻¹
  refine h_scaled.congr_fun fun n => ?_
  dsimp [F]
  rw [intervalIntegral.integral_const_mul,
    integral_exp_mul_crossFactor_shift hΔ (n + K) hwr]
  have h_pi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h_exp :
      Complex.exp (((Δ_phi + (n : ℝ) : ℝ) : ℂ) * wl - (K : ℂ) * wr) *
        Complex.exp (((Δ_phi + ((n + K : ℕ) : ℝ) : ℝ) : ℂ) * wr) =
      Complex.exp (((Δ_phi + (n : ℝ) : ℝ) : ℂ) * (wl + wr)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h4_sq : (4 : ℝ) ^ (2 * Δ_phi) = (4 : ℝ) ^ Δ_phi * (4 : ℝ) ^ Δ_phi := by
    rw [← Real.rpow_add (by norm_num), two_mul]
  rw [h4_sq, ← h_exp]
  push_cast
  linear_combination
    -(2 * (((4 : ℝ) ^ Δ_phi : ℝ) : ℂ) * (((4 : ℝ) ^ Δ_phi : ℝ) : ℂ) *
      (pochhammerCoeff (2 * Δ_phi) n : ℂ) *
      (pochhammerCoeff (2 * Δ_phi) (n + K) : ℂ) *
      Complex.exp ((((Δ_phi : ℂ) + (n : ℂ)) * wl - (K : ℂ) * wr)) *
      Complex.exp ((((Δ_phi : ℂ) + ((n : ℂ) + (K : ℂ))) * wr))) *
      (inv_mul_cancel₀ h_pi)

/-- Large-spin limit of the full $[-\pi, \pi]$ integral `identityProjSpinFull` along the real-axis
contour $\sigma_l = \sigma + 1/(2k), \sigma_r = -1/(2k)$:
$$\lim_{k \to \infty} (2k)^{1 - 2\Delta_\phi}
  \operatorname{identityProjSpinFull}(\Delta_\phi, 2k, \sigma_l, \sigma_r)
  = \operatorname{universalLaplaceReal}(\Delta_\phi, \sigma).$$ -/
theorem tendsto_identityProjSpinFull_real {Δ_phi : ℝ} (hΔ : 0 < Δ_phi)
    {σ : ℝ} (hσ : σ < 0) :
    Tendsto
      (fun k : ℕ =>
        (((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) : ℝ) : ℂ) *
          identityProjSpinFull Δ_phi (2 * (k : ℤ))
            (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ)))
      atTop (𝓝 (universalLaplaceReal Δ_phi σ : ℂ)) := by
  have h2Δ : 0 < 2 * Δ_phi := by positivity
  have h_lim :=
    ((tendsto_rpow_mul_tsum_pochhammerCoeff h2Δ hσ).comp
      (tendsto_id.const_mul_atTop' (by norm_num : 0 < 2))).const_mul
      (2 * (4 : ℝ) ^ (2 * Δ_phi) * Real.exp (Δ_phi * σ))
  have h_target :
      (2 * (4 : ℝ) ^ (2 * Δ_phi) * Real.exp (Δ_phi * σ)) *
          ((Real.Gamma (2 * Δ_phi))⁻¹ * (1 - Real.exp σ) ^ (- (2 * Δ_phi))) =
        universalLaplaceReal Δ_phi σ := by
    dsimp [universalLaplaceReal]
    ring
  rw [h_target] at h_lim
  have h_complex := (Complex.continuous_ofReal.tendsto _).comp h_lim
  have h_ev : ∀ᶠ k : ℕ in atTop, 0 < k ∧ σ + 1 / (2 * (k : ℝ)) < 0 := by
    have h_tendsto : Tendsto (fun k : ℕ => σ + 1 / (2 * (k : ℝ))) atTop (𝓝 (σ + 0)) :=
      tendsto_const_nhds.add
        (tendsto_const_nhds.div_atTop
          (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
            (tendsto_natCast_atTop_atTop (R := ℝ))))
    rw [add_zero] at h_tendsto
    exact (eventually_gt_atTop 0).and (h_tendsto.eventually (gt_mem_nhds hσ))
  refine h_complex.congr' ?_
  filter_upwards [h_ev] with k ⟨hk, hσl⟩
  set wl : ℂ := ((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)
  set wr : ℂ := ((-1 / (2 * (k : ℝ)) : ℝ) : ℂ)
  have hwl : wl ∈ UcDisk := by rw [mem_UcDisk_iff]; simpa [wl] using hσl
  have hwr : wr ∈ UcDisk := by
    rw [mem_UcDisk_iff]
    exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
  have h_sum := hasSum_identityProjSpinFull hΔ (2 * k) hwl hwr
  have h_cast_2k : ((2 * k : ℕ) : ℤ) = 2 * (k : ℤ) := by push_cast; rfl
  rw [h_cast_2k] at h_sum
  have h_add : wl + wr = (σ : ℂ) := by dsimp [wl, wr]; push_cast; ring
  rw [h_add] at h_sum
  have h_sum_real :
      HasSum
        (fun n : ℕ =>
          ((((2 * (4 : ℝ) ^ (2 * Δ_phi) * Real.exp (Δ_phi * σ)) *
            (pochhammerCoeff (2 * Δ_phi) n * pochhammerCoeff (2 * Δ_phi) (n + 2 * k) *
              (Real.exp σ) ^ n) : ℝ) : ℂ)))
        (identityProjSpinFull Δ_phi (2 * (k : ℤ)) wl wr) := by
    refine h_sum.congr_fun fun n => ?_
    have hexp_cast :
        Complex.exp (((Δ_phi + (n : ℝ) : ℝ) : ℂ) * (σ : ℂ)) =
          ((Real.exp (Δ_phi * σ) * (Real.exp σ) ^ n : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, add_mul, Real.exp_add, Real.exp_nat_mul]
    rw [hexp_cast]
    push_cast
    ring
  rw [← h_sum_real.tsum_eq, ← Complex.ofReal_tsum, tsum_mul_left]
  dsimp [Function.comp_def]
  push_cast
  ring

/-!
### Vanishing of the Outer $\theta$-Integral on $[-\pi, -\pi/2] \cup [\pi/2, \pi]$
-/

lemma one_sub_exp_add_mul_I_mem_slitPlane {u : ℝ} (hu : u < 0) (s θ : ℝ) :
    1 - Complex.exp ((u : ℂ) + ((s * θ : ℝ) : ℂ) * I) ∈ Complex.slitPlane := by
  refine one_sub_exp_mem_slitPlane ?_
  rw [mem_UcDisk_iff]
  simpa using hu

lemma one_le_norm_one_sub_exp_of_cos_nonpos {u s θ : ℝ}
    (hcos : Real.cos (s * θ) ≤ 0) :
    1 ≤ ‖1 - Complex.exp ((u : ℂ) + ((s * θ : ℝ) : ℂ) * I)‖ := by
  have h_re : 1 ≤ (1 - Complex.exp ((u : ℂ) + ((s * θ : ℝ) : ℂ) * I)).re := by
    simp only [sub_re, one_re, Complex.exp_re, add_re, ofReal_re, mul_re, I_re, mul_zero,
      ofReal_im, I_im, mul_one, sub_zero, add_zero, add_im, mul_im, zero_add]
    nlinarith [Real.exp_pos u]
  exact h_re.trans (Complex.re_le_norm _)

lemma norm_one_sub_exp_cpow_le_one_of_cos_nonpos {u s θ α : ℝ}
    (hcos : Real.cos (s * θ) ≤ 0) (hα : α ≤ 0) :
    ‖(1 - Complex.exp ((u : ℂ) + ((s * θ : ℝ) : ℂ) * I)) ^ (α : ℂ)‖ ≤ 1 := by
  have h1 : 1 ≤ ‖1 - Complex.exp ((u : ℂ) + ((s * θ : ℝ) : ℂ) * I)‖ :=
    one_le_norm_one_sub_exp_of_cos_nonpos hcos
  have h_pos : 0 < ‖1 - Complex.exp ((u : ℂ) + ((s * θ : ℝ) : ℂ) * I)‖ := by linarith
  have h_ne : 1 - Complex.exp ((u : ℂ) + ((s * θ : ℝ) : ℂ) * I) ≠ 0 :=
    norm_pos_iff.mp h_pos
  have h_norm :
      ‖(1 - Complex.exp ((u : ℂ) + ((s * θ : ℝ) : ℂ) * I)) ^ (α : ℂ)‖ =
        ‖1 - Complex.exp ((u : ℂ) + ((s * θ : ℝ) : ℂ) * I)‖ ^ α := by
    rw [cpow_def_of_ne_zero h_ne, Complex.norm_exp]
    have hre : (Complex.log (1 - Complex.exp ((u : ℂ) + ((s * θ : ℝ) : ℂ) * I)) * (α : ℂ)).re =
        Real.log ‖1 - Complex.exp ((u : ℂ) + ((s * θ : ℝ) : ℂ) * I)‖ * α := by
      simp [Complex.mul_re, Complex.log_re]
    rw [hre, Real.rpow_def_of_pos h_pos]
  rw [h_norm]
  exact Real.rpow_le_one_of_one_le_of_nonpos h1 hα

lemma hasDerivAt_one_sub_exp_cpow {u : ℝ} (hu : u < 0) (s α θ : ℝ) :
    HasDerivAt
      (fun x : ℝ => (1 - Complex.exp ((u : ℂ) + ((s * x : ℝ) : ℂ) * I)) ^ (α : ℂ))
      ((α : ℂ) *
        (1 - Complex.exp ((u : ℂ) + ((s * θ : ℝ) : ℂ) * I)) ^ (((α - 1 : ℝ) : ℂ)) *
        (- (Complex.exp ((u : ℂ) + ((s * θ : ℝ) : ℂ) * I) * ((s : ℂ) * I))))
      θ := by
  have h1 : HasDerivAt (fun x : ℝ => (u : ℂ) + ((s * x : ℝ) : ℂ) * I) ((s : ℂ) * I) θ := by
    have h_lin : HasDerivAt (fun x : ℝ => s * x) s θ := by
      simpa using (hasDerivAt_id θ).const_mul s
    simpa using ((h_lin.ofReal_comp).mul_const I).const_add (u : ℂ)
  have h2 : HasDerivAt (fun x : ℝ => 1 - Complex.exp ((u : ℂ) + ((s * x : ℝ) : ℂ) * I))
      (- (Complex.exp ((u : ℂ) + ((s * θ : ℝ) : ℂ) * I) * ((s : ℂ) * I))) θ := by
    have h_sub := (hasDerivAt_const θ (1 : ℂ)).sub h1.cexp
    rw [zero_sub] at h_sub
    exact h_sub
  have h_cpow : HasDerivAt (fun z : ℂ => z ^ (α : ℂ))
      ((α : ℂ) * (1 - Complex.exp ((u : ℂ) + ((s * θ : ℝ) : ℂ) * I)) ^ ((α : ℂ) - 1) * 1)
      (1 - Complex.exp ((u : ℂ) + ((s * θ : ℝ) : ℂ) * I)) :=
    (hasDerivAt_id _).cpow_const (one_sub_exp_add_mul_I_mem_slitPlane hu s θ)
  have h3 := h_cpow.scomp θ h2
  refine h3.congr_deriv ?_
  rw [smul_eq_mul]
  have h_sub : (α : ℂ) - 1 = ((α - 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [h_sub]
  ring

lemma continuous_one_sub_exp_cpow {u : ℝ} (hu : u < 0) (s α : ℝ) :
    Continuous (fun x : ℝ =>
      (1 - Complex.exp ((u : ℂ) + ((s * x : ℝ) : ℂ) * I)) ^ (α : ℂ)) :=
  continuous_iff_continuousAt.mpr fun θ =>
    (hasDerivAt_one_sub_exp_cpow hu s α θ).continuousAt

/-- One-step integration by parts bound for $\int_a^b e^{-i K \theta} g(\theta) \, d\theta$:
if $a \le b$, $K > 0$, $g$ has continuous derivative $g'$ on $\mathbb{R}$, and
$\|g(\theta)\| \le M_0, \|g'(\theta)\| \le M_1$ on $[a, b]$, then
$$\left\|\int_a^b e^{-i K \theta} g(\theta) \, d\theta\right\| \le
  \frac{2 M_0 + M_1 (b - a)}{K}.$$ -/
lemma norm_integral_exp_neg_mul_I_le {g g' : ℝ → ℂ} {a b K M0 M1 : ℝ}
    (hab : a ≤ b) (hK : 0 < K) (_hM0 : 0 ≤ M0) (_hM1 : 0 ≤ M1)
    (hg'_cont : Continuous g')
    (hderiv : ∀ θ : ℝ, HasDerivAt g (g' θ) θ)
    (hbound0 : ∀ θ ∈ Icc a b, ‖g θ‖ ≤ M0)
    (hbound1 : ∀ θ ∈ Icc a b, ‖g' θ‖ ≤ M1) :
    ‖∫ θ in a..b, Complex.exp (- (K : ℂ) * (θ : ℂ) * I) * g θ‖ ≤
      (2 * M0 + M1 * (b - a)) / K := by
  have hg_cont : Continuous g :=
    continuous_iff_continuousAt.mpr fun θ => (hderiv θ).continuousAt
  have hK_c : (K : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hK.ne'
  set E : ℝ → ℂ := fun θ => (I / (K : ℂ)) * Complex.exp (- (K : ℂ) * (θ : ℂ) * I)
  have hE_deriv : ∀ θ : ℝ, HasDerivAt E (Complex.exp (- (K : ℂ) * (θ : ℂ) * I)) θ := by
    intro θ
    have h1 : HasDerivAt (fun x : ℝ => - (K : ℂ) * (x : ℂ) * I) (- (K : ℂ) * I) θ := by
      simpa [mul_assoc] using
        (((hasDerivAt_id θ).ofReal_comp).const_mul (- (K : ℂ))).mul_const I
    have h2 := (h1.cexp).const_mul (I / (K : ℂ))
    refine h2.congr_deriv ?_
    calc
      I / (K : ℂ) * (Complex.exp (- (K : ℂ) * (θ : ℂ) * I) * (- (K : ℂ) * I))
        = (-(I * I) * ((K : ℂ) / (K : ℂ))) * Complex.exp (- (K : ℂ) * (θ : ℂ) * I) := by ring
      _ = Complex.exp (- (K : ℂ) * (θ : ℂ) * I) := by
        rw [Complex.I_mul_I, neg_neg, div_self hK_c, one_mul, one_mul]
  have hE_norm : ∀ θ : ℝ, ‖E θ‖ = 1 / K := by
    intro θ
    dsimp [E]
    rw [norm_mul, norm_div, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg hK.le,
      Complex.norm_exp]
    have hre : (- (K : ℂ) * (θ : ℂ) * I).re = 0 := by simp [Complex.mul_re]
    rw [hre, Real.exp_zero, mul_one]
  have h_prod_deriv : ∀ θ ∈ uIcc a b,
      HasDerivAt (fun x => E x * g x)
        (Complex.exp (- (K : ℂ) * (θ : ℂ) * I) * g θ + E θ * g' θ) θ :=
    fun θ _ => (hE_deriv θ).mul (hderiv θ)
  have h_int1 : IntervalIntegrable
      (fun θ => Complex.exp (- (K : ℂ) * (θ : ℂ) * I) * g θ) volume a b :=
    ((by fun_prop : Continuous _).mul hg_cont).intervalIntegrable a b
  have h_int2 : IntervalIntegrable (fun θ => E θ * g' θ) volume a b :=
    ((by dsimp [E]; fun_prop : Continuous E).mul hg'_cont).intervalIntegrable a b
  have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt h_prod_deriv (h_int1.add h_int2)
  rw [intervalIntegral.integral_add h_int1 h_int2] at h_ftc
  have h_ibp :
      (∫ θ in a..b, Complex.exp (- (K : ℂ) * (θ : ℂ) * I) * g θ) =
        E b * g b - E a * g a - ∫ θ in a..b, E θ * g' θ := by
    linear_combination h_ftc
  have ha_mem : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb_mem : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have h_norm_b : ‖E b * g b‖ ≤ M0 / K := by
    rw [norm_mul, hE_norm b, one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right (hbound0 b hb_mem) hK.le
  have h_norm_a : ‖E a * g a‖ ≤ M0 / K := by
    rw [norm_mul, hE_norm a, one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right (hbound0 a ha_mem) hK.le
  have h_norm_int : ‖∫ θ in a..b, E θ * g' θ‖ ≤ (M1 / K) * (b - a) := by
    have h_pt : ∀ θ ∈ Ioc a b, ‖E θ * g' θ‖ ≤ M1 / K := by
      intro θ hθ
      rw [norm_mul, hE_norm θ, one_div_mul_eq_div]
      exact div_le_div_of_nonneg_right (hbound1 θ ⟨hθ.1.le, hθ.2⟩) hK.le
    have h_le := intervalIntegral.norm_integral_le_of_norm_le hab
      (Eventually.of_forall h_pt)
      (intervalIntegrable_const (μ := volume) (c := M1 / K))
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm] at h_le
    exact h_le
  rw [h_ibp]
  calc
    ‖E b * g b - E a * g a - ∫ θ in a..b, E θ * g' θ‖
      ≤ ‖E b * g b - E a * g a‖ + ‖∫ θ in a..b, E θ * g' θ‖ := norm_sub_le _ _
    _ ≤ (‖E b * g b‖ + ‖E a * g a‖) + ‖∫ θ in a..b, E θ * g' θ‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ (M0 / K + M0 / K) + (M1 / K) * (b - a) :=
      add_le_add (add_le_add h_norm_b h_norm_a) h_norm_int
    _ = (2 * M0 + M1 * (b - a)) / K := by ring

lemma integral_minus_pi_to_pi_sub_half {f : ℝ → ℂ} (hf : Continuous f) :
    (∫ θ in (-π)..π, f θ) - (∫ θ in (-π / 2)..(π / 2), f θ) =
      (∫ θ in (-π)..(-π / 2), f θ) + (∫ θ in (π / 2)..π, f θ) := by
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := volume) (-π) (-π / 2))
    (hf.intervalIntegrable (μ := volume) (-π / 2) (π / 2))
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := volume) (-π) (π / 2))
    (hf.intervalIntegrable (μ := volume) (π / 2) π)
  linear_combination -h1 - h2

/-- Bound on $\int_a^b e^{-i K \theta} (1 - e^{\sigma_l - i\theta})^{-2\Delta_\phi}
(1 - e^{\sigma_r + i\theta})^{-2\Delta_\phi} \, d\theta$ on any interval $[a, b]$ where
$\cos \theta \le 0$: for $\Delta_\phi > 0$, $\sigma_l < 0, \sigma_r < 0$, and $K > 0$,
$$\left\|\int_a^b e^{-i K \theta}
  (1 - e^{\sigma_l - i\theta})^{-2\Delta_\phi}
  (1 - e^{\sigma_r + i\theta})^{-2\Delta_\phi} \, d\theta\right\| \le
  \frac{2 + 4\Delta_\phi (b - a)}{K}.$$ -/
lemma norm_integral_binomialProd_le_of_cos_nonpos
    {Δ_phi σl σr a b K : ℝ} (hΔ : 0 < Δ_phi) (hσl : σl < 0) (hσr : σr < 0)
    (hab : a ≤ b) (hK : 0 < K) (hcos : ∀ θ ∈ Icc a b, Real.cos θ ≤ 0) :
    ‖∫ θ in a..b,
      Complex.exp (- (K : ℂ) * (θ : ℂ) * I) *
        ((1 - Complex.exp ((σl : ℂ) + ((-1 * θ : ℝ) : ℂ) * I)) ^ ((-2 * Δ_phi : ℝ) : ℂ) *
          (1 - Complex.exp ((σr : ℂ) + ((1 * θ : ℝ) : ℂ) * I)) ^ ((-2 * Δ_phi : ℝ) : ℂ))‖ ≤
      (2 + (4 * Δ_phi) * (b - a)) / K := by
  set α : ℝ := -2 * Δ_phi
  set gl : ℝ → ℂ := fun θ =>
    (1 - Complex.exp ((σl : ℂ) + ((-1 * θ : ℝ) : ℂ) * I)) ^ (α : ℂ)
  set gr : ℝ → ℂ := fun θ =>
    (1 - Complex.exp ((σr : ℂ) + ((1 * θ : ℝ) : ℂ) * I)) ^ (α : ℂ)
  set gl' : ℝ → ℂ := fun θ =>
    (α : ℂ) *
      (1 - Complex.exp ((σl : ℂ) + ((-1 * θ : ℝ) : ℂ) * I)) ^ (((α - 1 : ℝ) : ℂ)) *
      (- (Complex.exp ((σl : ℂ) + ((-1 * θ : ℝ) : ℂ) * I) * ((-1 : ℝ) : ℂ) * I))
  set gr' : ℝ → ℂ := fun θ =>
    (α : ℂ) *
      (1 - Complex.exp ((σr : ℂ) + ((1 * θ : ℝ) : ℂ) * I)) ^ (((α - 1 : ℝ) : ℂ)) *
      (- (Complex.exp ((σr : ℂ) + ((1 * θ : ℝ) : ℂ) * I) * ((1 : ℝ) : ℂ) * I))
  have hgl_deriv : ∀ θ : ℝ, HasDerivAt gl (gl' θ) θ := by
    intro θ
    simpa [gl, gl', mul_assoc] using hasDerivAt_one_sub_exp_cpow hσl (-1) α θ
  have hgr_deriv : ∀ θ : ℝ, HasDerivAt gr (gr' θ) θ := by
    intro θ
    simpa [gr, gr', mul_assoc] using hasDerivAt_one_sub_exp_cpow hσr 1 α θ
  have hgl_cont : Continuous gl := continuous_one_sub_exp_cpow hσl (-1) α
  have hgr_cont : Continuous gr := continuous_one_sub_exp_cpow hσr 1 α
  have hgl'_cont : Continuous gl' := by
    dsimp [gl']
    exact (continuous_const.mul (continuous_one_sub_exp_cpow hσl (-1) (α - 1))).mul
      (by fun_prop)
  have hgr'_cont : Continuous gr' := by
    dsimp [gr']
    exact (continuous_const.mul (continuous_one_sub_exp_cpow hσr 1 (α - 1))).mul
      (by fun_prop)
  have h_ibp := norm_integral_exp_neg_mul_I_le (M0 := 1) (M1 := 4 * Δ_phi)
    hab hK zero_le_one (by positivity)
    ((hgl'_cont.mul hgr_cont).add (hgl_cont.mul hgr'_cont))
    (fun θ => (hgl_deriv θ).mul (hgr_deriv θ))
  rw [two_mul, one_add_one_eq_two] at h_ibp
  refine h_ibp ?_ ?_
  · intro θ hθ
    have hcos_l : Real.cos (-1 * θ) ≤ 0 := by
      rw [neg_one_mul, Real.cos_neg]; exact hcos θ hθ
    have hcos_r : Real.cos (1 * θ) ≤ 0 := by
      rw [one_mul]; exact hcos θ hθ
    change ‖gl θ * gr θ‖ ≤ 1
    rw [norm_mul (gl θ) (gr θ)]
    calc
      ‖gl θ‖ * ‖gr θ‖ ≤ 1 * 1 :=
        mul_le_mul
          (norm_one_sub_exp_cpow_le_one_of_cos_nonpos hcos_l (by dsimp [α]; linarith))
          (norm_one_sub_exp_cpow_le_one_of_cos_nonpos hcos_r (by dsimp [α]; linarith))
          (norm_nonneg _) zero_le_one
      _ = 1 := mul_one 1
  · intro θ hθ
    have hcos_l : Real.cos (-1 * θ) ≤ 0 := by
      rw [neg_one_mul, Real.cos_neg]; exact hcos θ hθ
    have hcos_r : Real.cos (1 * θ) ≤ 0 := by
      rw [one_mul]; exact hcos θ hθ
    have hgl_le : ‖gl θ‖ ≤ 1 :=
      norm_one_sub_exp_cpow_le_one_of_cos_nonpos hcos_l (by dsimp [α]; linarith)
    have hgr_le : ‖gr θ‖ ≤ 1 :=
      norm_one_sub_exp_cpow_le_one_of_cos_nonpos hcos_r (by dsimp [α]; linarith)
    have hgl'_le : ‖gl' θ‖ ≤ 2 * Δ_phi := by
      have h_norm_gl' :
          ‖gl' θ‖ = (2 * Δ_phi) *
            ‖(1 - Complex.exp ((σl : ℂ) + ((-1 * θ : ℝ) : ℂ) * I)) ^ (((α - 1 : ℝ) : ℂ))‖ *
            Real.exp σl := by
        have h_abs_α : |α| = 2 * Δ_phi := by
          dsimp [α]; rw [abs_of_neg (by linarith)]; ring
        simp [gl', h_abs_α, Complex.norm_exp]
      have hexp_le : Real.exp σl ≤ 1 := Real.exp_le_one_iff.mpr hσl.le
      have hcpow_le :
          ‖(1 - Complex.exp ((σl : ℂ) + ((-1 * θ : ℝ) : ℂ) * I)) ^ (((α - 1 : ℝ) : ℂ))‖ ≤ 1 :=
        norm_one_sub_exp_cpow_le_one_of_cos_nonpos hcos_l (by dsimp [α]; linarith)
      rw [h_norm_gl']
      calc
        2 * Δ_phi *
            ‖(1 - Complex.exp ((σl : ℂ) + ((-1 * θ : ℝ) : ℂ) * I)) ^ (((α - 1 : ℝ) : ℂ))‖ *
            Real.exp σl
          ≤ (2 * Δ_phi * 1) * 1 :=
            mul_le_mul
              (mul_le_mul_of_nonneg_left hcpow_le (by positivity))
              hexp_le (Real.exp_pos σl).le (by positivity)
        _ = 2 * Δ_phi := by ring
    have hgr'_le : ‖gr' θ‖ ≤ 2 * Δ_phi := by
      have h_norm_gr' :
          ‖gr' θ‖ = (2 * Δ_phi) *
            ‖(1 - Complex.exp ((σr : ℂ) + ((1 * θ : ℝ) : ℂ) * I)) ^ (((α - 1 : ℝ) : ℂ))‖ *
            Real.exp σr := by
        have h_abs_α : |α| = 2 * Δ_phi := by
          dsimp [α]; rw [abs_of_neg (by linarith)]; ring
        simp [gr', h_abs_α, Complex.norm_exp]
      have hexp_le : Real.exp σr ≤ 1 := Real.exp_le_one_iff.mpr hσr.le
      have hcpow_le :
          ‖(1 - Complex.exp ((σr : ℂ) + ((1 * θ : ℝ) : ℂ) * I)) ^ (((α - 1 : ℝ) : ℂ))‖ ≤ 1 :=
        norm_one_sub_exp_cpow_le_one_of_cos_nonpos hcos_r (by dsimp [α]; linarith)
      rw [h_norm_gr']
      calc
        2 * Δ_phi *
            ‖(1 - Complex.exp ((σr : ℂ) + ((1 * θ : ℝ) : ℂ) * I)) ^ (((α - 1 : ℝ) : ℂ))‖ *
            Real.exp σr
          ≤ (2 * Δ_phi * 1) * 1 :=
            mul_le_mul
              (mul_le_mul_of_nonneg_left hcpow_le (by positivity))
              hexp_le (Real.exp_pos σr).le (by positivity)
        _ = 2 * Δ_phi := by ring
    calc
      ‖gl' θ * gr θ + gl θ * gr' θ‖
        ≤ ‖gl' θ * gr θ‖ + ‖gl θ * gr' θ‖ := norm_add_le _ _
      _ = ‖gl' θ‖ * ‖gr θ‖ + ‖gl θ‖ * ‖gr' θ‖ := by rw [norm_mul (gl' θ), norm_mul (gl θ)]
      _ ≤ (2 * Δ_phi) * 1 + 1 * (2 * Δ_phi) :=
        add_le_add
          (mul_le_mul hgl'_le hgr_le (norm_nonneg _) (by positivity))
          (mul_le_mul hgl_le hgr'_le (norm_nonneg _) zero_le_one)
      _ = 4 * Δ_phi := by ring

/-- Factorization of `crossIdentity Δ_phi (wl - i θ) (wr + i θ)` separating the $\theta$-independent
prefactor $4^{2\Delta_\phi} e^{\Delta_\phi (w_l + w_r)}$ from the $2\pi$-periodic factors. -/
lemma crossIdentity_shift_eq (Δ_phi : ℝ) (wl wr : ℂ) (θ : ℝ) :
    crossIdentity Δ_phi (wl - (θ : ℂ) * I) (wr + (θ : ℂ) * I) =
      (((4 : ℝ) ^ (2 * Δ_phi) : ℝ) : ℂ) * Complex.exp ((Δ_phi : ℂ) * (wl + wr)) *
        (1 - Complex.exp (wl - (θ : ℂ) * I)) ^ (- (2 * Δ_phi : ℂ)) *
        (1 - Complex.exp (wr + (θ : ℂ) * I)) ^ (- (2 * Δ_phi : ℂ)) := by
  dsimp [crossIdentity, crossFactor]
  have h4_cast : (4 : ℂ) ^ (Δ_phi : ℂ) = (((4 : ℝ) ^ Δ_phi : ℝ) : ℂ) := by
    have : (4 : ℂ) = ((4 : ℝ) : ℂ) := by norm_cast
    rw [this, ← Complex.ofReal_cpow (by norm_num)]
  have h4_sq : (4 : ℝ) ^ (2 * Δ_phi) = (4 : ℝ) ^ Δ_phi * (4 : ℝ) ^ Δ_phi := by
    rw [← Real.rpow_add (by norm_num), two_mul]
  have hexp :
      Complex.exp ((Δ_phi : ℂ) * (wl - (θ : ℂ) * I)) *
        Complex.exp ((Δ_phi : ℂ) * (wr + (θ : ℂ) * I)) =
      Complex.exp ((Δ_phi : ℂ) * (wl + wr)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [h4_cast, h4_sq]
  push_cast
  linear_combination
    ((((4 : ℝ) ^ Δ_phi : ℝ) : ℂ) * (((4 : ℝ) ^ Δ_phi : ℝ) : ℂ) *
      (1 - Complex.exp (wl - (θ : ℂ) * I)) ^ (- (2 * Δ_phi : ℂ)) *
      (1 - Complex.exp (wr + (θ : ℂ) * I)) ^ (- (2 * Δ_phi : ℂ))) * hexp

/-- The rescaled outer integral `identityProjSpinFull - identityProjSpin` on
$[-\pi, -\pi/2] \cup [\pi/2, \pi]$ is $O((2k)^{-2\Delta_\phi})$ and vanishes as $k \to \infty$
for all $\Delta_\phi > 0$. -/
lemma tendsto_identityProjSpinFull_sub_identityProjSpin_real {Δ_phi : ℝ} (hΔ : 0 < Δ_phi)
    {σ : ℝ} (hσ : σ < 0) :
    Tendsto
      (fun k : ℕ =>
        (((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) : ℝ) : ℂ) *
          (identityProjSpinFull Δ_phi (2 * (k : ℤ))
              (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ)) -
            identityProjSpin Δ_phi (2 * (k : ℤ))
              (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ))))
      atTop (𝓝 0) := by
  set C_out : ℝ :=
    π⁻¹ * ((4 : ℝ) ^ (2 * Δ_phi) * Real.exp (Δ_phi * σ + 1)) *
      (2 * (2 + (4 * Δ_phi) * (π / 2)))
  have h_zero : Tendsto (fun k : ℕ => C_out * (2 * (k : ℝ)) ^ (-2 * Δ_phi)) atTop (𝓝 0) := by
    have h_2k : Tendsto (fun k : ℕ => 2 * (k : ℝ)) atTop atTop :=
      Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
        (tendsto_natCast_atTop_atTop (R := ℝ))
    have h_exp : -2 * Δ_phi = - (2 * Δ_phi) := by ring
    rw [h_exp]
    simpa using ((tendsto_rpow_neg_atTop (by positivity)).comp h_2k).const_mul C_out
  refine squeeze_zero_norm' ?_ h_zero
  have h_ev : ∀ᶠ k : ℕ in atTop, 1 ≤ k ∧ σ + 1 / (2 * (k : ℝ)) < 0 := by
    have h_tendsto : Tendsto (fun k : ℕ => σ + 1 / (2 * (k : ℝ))) atTop (𝓝 (σ + 0)) :=
      tendsto_const_nhds.add
        (tendsto_const_nhds.div_atTop
          (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
            (tendsto_natCast_atTop_atTop (R := ℝ))))
    rw [add_zero] at h_tendsto
    exact (eventually_ge_atTop 1).and (h_tendsto.eventually (gt_mem_nhds hσ))
  filter_upwards [h_ev] with k ⟨hk1, hσl⟩
  set K : ℝ := 2 * (k : ℝ)
  have hK_pos : 0 < K := by dsimp [K]; exact_mod_cast (by omega : 0 < 2 * k)
  set σl : ℝ := σ + 1 / K
  set σr : ℝ := -1 / K
  have hσr : σr < 0 := div_neg_of_neg_of_pos (by norm_num) hK_pos
  set wl : ℂ := (σl : ℂ)
  set wr : ℂ := (σr : ℂ)
  have hwl : wl ∈ UcDisk := by rw [mem_UcDisk_iff]; simpa [wl] using hσl
  have hwr : wr ∈ UcDisk := by rw [mem_UcDisk_iff]; simpa [wr] using hσr
  let f : ℝ → ℂ := fun θ =>
    Complex.exp (- ((2 * (k : ℤ) : ℤ) : ℂ) * (wr + (θ : ℂ) * I)) *
      crossIdentity Δ_phi (wl - (θ : ℂ) * I) (wr + (θ : ℂ) * I)
  have hf_cont : Continuous f :=
    (by fun_prop : Continuous _).mul (continuous_crossIdentity_shift Δ_phi hwl hwr)
  have h_diff :
      identityProjSpinFull Δ_phi (2 * (k : ℤ)) wl wr -
        identityProjSpin Δ_phi (2 * (k : ℤ)) wl wr =
      (π : ℂ)⁻¹ * ((∫ θ in (-π)..(-π / 2), f θ) + (∫ θ in (π / 2)..π, f θ)) := by
    dsimp [identityProjSpinFull, identityProjSpin, f]
    rw [← mul_sub, integral_minus_pi_to_pi_sub_half hf_cont]
  set c_k : ℂ :=
    (((4 : ℝ) ^ (2 * Δ_phi) * Real.exp (Δ_phi * σ + 1) : ℝ) : ℂ)
  let h_bin : ℝ → ℂ := fun θ =>
    Complex.exp (- (K : ℂ) * (θ : ℂ) * I) *
      ((1 - Complex.exp ((σl : ℂ) + ((-1 * θ : ℝ) : ℂ) * I)) ^ ((-2 * Δ_phi : ℝ) : ℂ) *
        (1 - Complex.exp ((σr : ℂ) + ((1 * θ : ℝ) : ℂ) * I)) ^ ((-2 * Δ_phi : ℝ) : ℂ))
  have hf_eq : ∀ θ : ℝ, f θ = c_k * h_bin θ := by
    intro θ
    dsimp only [f, h_bin]
    rw [crossIdentity_shift_eq]
    have h_add : wl + wr = (σ : ℂ) := by dsimp [wl, wr, σl, σr]; push_cast; ring
    have h_l : wl - (θ : ℂ) * I = (σl : ℂ) + ((-1 * θ : ℝ) : ℂ) * I := by
      dsimp [wl]; push_cast; ring
    have h_r : wr + (θ : ℂ) * I = (σr : ℂ) + ((1 * θ : ℝ) : ℂ) * I := by
      dsimp [wr]; push_cast; ring
    have h_α : (- (2 * Δ_phi : ℂ)) = ((-2 * Δ_phi : ℝ) : ℂ) := by push_cast; ring
    have h_exp :
        Complex.exp (- ((2 * (k : ℤ) : ℤ) : ℂ) * ((σr : ℂ) + ((1 * θ : ℝ) : ℂ) * I)) *
          Complex.exp ((Δ_phi : ℂ) * (wl + wr)) =
        ((Real.exp (Δ_phi * σ + 1) : ℝ) : ℂ) *
          Complex.exp (- (K : ℂ) * (θ : ℂ) * I) := by
      rw [h_add, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      dsimp [σr, K]
      have hk_ne : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      push_cast
      field_simp
      ring
    rw [h_l, h_r, h_α]
    have hc_k : c_k = (((4 : ℝ) ^ (2 * Δ_phi) : ℝ) : ℂ) *
        ((Real.exp (Δ_phi * σ + 1) : ℝ) : ℂ) := by
      dsimp [c_k]; push_cast; rfl
    rw [hc_k]
    linear_combination
      ((((4 : ℝ) ^ (2 * Δ_phi) : ℝ) : ℂ) *
        (1 - Complex.exp ((σl : ℂ) + ((-1 * θ : ℝ) : ℂ) * I)) ^ ((-2 * Δ_phi : ℝ) : ℂ) *
        (1 - Complex.exp ((σr : ℂ) + ((1 * θ : ℝ) : ℂ) * I)) ^ ((-2 * Δ_phi : ℝ) : ℂ)) * h_exp
  simp_rw [hf_eq, intervalIntegral.integral_const_mul, ← mul_add] at h_diff
  have hcos1 : ∀ θ ∈ Icc (-π) (-π / 2), Real.cos θ ≤ 0 := by
    intro θ hθ
    rw [← Real.cos_neg]
    exact Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith [hθ.2])
      (by linarith [hθ.1, Real.pi_pos])
  have hcos2 : ∀ θ ∈ Icc (π / 2) π, Real.cos θ ≤ 0 := by
    intro θ hθ
    exact Real.cos_nonpos_of_pi_div_two_le_of_le hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have h_b1 := norm_integral_binomialProd_le_of_cos_nonpos hΔ hσl hσr
    (by linarith [Real.pi_pos] : -π ≤ -π / 2) hK_pos hcos1
  have h_b2 := norm_integral_binomialProd_le_of_cos_nonpos hΔ hσl hσr
    (by linarith [Real.pi_pos] : π / 2 ≤ π) hK_pos hcos2
  have h_len1 : -π / 2 - -π = π / 2 := by ring
  have h_len2 : π - π / 2 = π / 2 := by ring
  rw [h_len1] at h_b1
  rw [h_len2] at h_b2
  rw [h_diff, norm_mul, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity : 0 ≤ K ^ (1 - 2 * Δ_phi)),
    norm_inv, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
    Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h_sum_b :
      ‖(∫ θ in (-π)..(-π / 2), h_bin θ) + (∫ θ in (π / 2)..π, h_bin θ)‖ ≤
        (2 * (2 + (4 * Δ_phi) * (π / 2))) / K := by
    calc
      ‖(∫ θ in (-π)..(-π / 2), h_bin θ) + (∫ θ in (π / 2)..π, h_bin θ)‖
        ≤ ‖∫ θ in (-π)..(-π / 2), h_bin θ‖ + ‖∫ θ in (π / 2)..π, h_bin θ‖ := norm_add_le _ _
      _ ≤ (2 + (4 * Δ_phi) * (π / 2)) / K + (2 + (4 * Δ_phi) * (π / 2)) / K :=
        add_le_add h_b1 h_b2
      _ = (2 * (2 + (4 * Δ_phi) * (π / 2))) / K := by ring
  have h_rpow : K ^ (1 - 2 * Δ_phi) / K = K ^ (-2 * Δ_phi) := by
    have : K ^ (1 - 2 * Δ_phi) / K = K ^ (1 - 2 * Δ_phi) * K ^ (- (1 : ℝ)) := by
      rw [Real.rpow_neg hK_pos.le, Real.rpow_one, div_eq_mul_inv]
    rw [this, ← Real.rpow_add hK_pos]
    ring_nf
  calc
    K ^ (1 - 2 * Δ_phi) *
        (π⁻¹ * ((4 : ℝ) ^ (2 * Δ_phi) * Real.exp (Δ_phi * σ + 1) *
          ‖(∫ θ in (-π)..(-π / 2), h_bin θ) + (∫ θ in (π / 2)..π, h_bin θ)‖))
      ≤ K ^ (1 - 2 * Δ_phi) *
          (π⁻¹ * ((4 : ℝ) ^ (2 * Δ_phi) * Real.exp (Δ_phi * σ + 1) *
            ((2 * (2 + (4 * Δ_phi) * (π / 2))) / K))) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h_sum_b (by positivity)) (by positivity))
          (by positivity)
    _ = C_out * (K ^ (1 - 2 * Δ_phi) / K) := by dsimp [C_out]; ring
    _ = C_out * K ^ (-2 * Δ_phi) := by rw [h_rpow]

/-- **Large-Spin Asymptotics of the $t$-Channel Identity Projection (`identityProjSpin`)**:
for every $\Delta_\phi > 0$ and $\sigma < 0$,
$$\lim_{k \to \infty} (2k)^{1 - 2\Delta_\phi}
  \operatorname{identityProjSpin}\!\left(\Delta_\phi, 2k,
    \sigma + \frac{1}{2k}, -\frac{1}{2k}\right)
  = \operatorname{universalLaplaceReal}(\Delta_\phi, \sigma).$$ -/
theorem tendsto_identityProjSpin_real {Δ_phi : ℝ} (hΔ : 0 < Δ_phi)
    {σ : ℝ} (hσ : σ < 0) :
    Tendsto
      (fun k : ℕ =>
        (((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) : ℝ) : ℂ) *
          identityProjSpin Δ_phi (2 * (k : ℤ))
            (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ)))
      atTop (𝓝 (universalLaplaceReal Δ_phi σ : ℂ)) := by
  have h_full := tendsto_identityProjSpinFull_real hΔ hσ
  have h_outer := tendsto_identityProjSpinFull_sub_identityProjSpin_real hΔ hσ
  have h_sub := h_full.sub h_outer
  rw [sub_zero] at h_sub
  refine h_sub.congr fun k => ?_
  ring


/-- Holomorphy of `universalLaplace Δ_phi` on $\operatorname{UcDisk}$. -/
theorem differentiableOn_universalLaplace (Δ_phi : ℝ) :
    DifferentiableOn ℂ (universalLaplace Δ_phi) UcDisk := by
  intro z hz
  have h_exp : DifferentiableAt ℂ (fun z => Complex.exp ((Δ_phi : ℂ) * z)) z :=
    (differentiableAt_id.const_mul (Δ_phi : ℂ)).cexp
  have h_sub : DifferentiableAt ℂ (fun z => 1 - Complex.exp z) z :=
    (differentiableAt_const 1).sub differentiableAt_id.cexp
  have h_cpow : DifferentiableAt ℂ (fun z => (1 - Complex.exp z) ^ (- (2 * Δ_phi : ℂ))) z :=
    h_sub.cpow_const (one_sub_exp_mem_slitPlane hz)
  exact (((h_exp.const_mul _).mul h_cpow).const_mul _).differentiableWithinAt

