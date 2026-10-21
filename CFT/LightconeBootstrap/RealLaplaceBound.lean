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
import CFT.LightconeBootstrap.Gap

/-!
# Uniform Real-Axis Laplace Error Bounds for the Lightcone Bootstrap

This file establishes uniform quantitative error bounds on compact negative intervals
`[σ_minus, σ_plus] ⊂ (-∞, 0)` for the rescaled spin-`2k` Laplace transform
`(2k)^(1 - 2Δ_φ) L_{2k}(σ)` against the universal double-twist Laplace transform
`universalLaplaceReal Δ_phi σ`:

1. **Quantitative `O(K⁻¹)` Euler Gamma Limit
   (`exists_abs_rpow_mul_pochhammerCoeff_sub_inv_gamma_le`,
   `exists_uniform_bound_tsum_pochhammerCoeff_sub`)**:
   Using second-order mean-value bounds on the consecutive ratios of
   `M^(1 - a) (a)_M / M!` and telescoping to the limit `(Γ(a))⁻¹`, we prove an explicit `O(K⁻¹)`
   convergence rate for the binomial series of `identityProjSpinFull` uniformly on `σ ≤ σ_plus < 0`.

2. **Uniform `O((2k)^(-2Δ_φ))` Outer `θ`-Integral Bound
   (`exists_uniform_bound_identityProjSpinFull_sub_identityProjSpin_real`)**:
   Integration by parts on `[-π, -π/2] ∪ [π/2, π]` bounds the difference between the full and
   folded `t`-channel identity projections by `C * (2k)^(-2Δ_φ)` uniformly on `σ ≤ σ_plus < 0`.

3. **Uniform `O((2k)^(-α))` Real-Axis Laplace Bound on `[σ_minus, σ_plus]`
   (`exists_uniform_laplaceSpinReal_bounds`)**:
   Combining the `t`-channel twist-gap remainder bound with the identity projection bounds yields
   uniform upper and error bounds on `[σ_minus, σ_plus] ⊂ (-∞, 0)` for all `k ≥ 1` with exponent
   `α = min (2 * h_gap) (min 1 (2 * Δ_phi - 1))`.
-/

open Real Complex Topology Set Metric MeasureTheory Filter
open scoped ComplexConjugate

namespace CFT.LightconeBootstrap

/-!
## 1. Universal Asymptotic Spin-`J` Laplace Transform and Binomial Series
-/

/-- The folded `θ`-integral of the `t`-channel identity contribution `crossIdentity Δ_phi`
over `θ ∈ [-π/2, π/2]`:
`∫_{-π/2}^{π/2} (dθ / π) e^{-J (w_r + iθ)} G_id(w_l - iθ, w_r + iθ)`. -/
noncomputable def identityProjSpin (Δ_phi : ℝ) (J : ℤ) (wl wr : ℂ) : ℂ :=
  (π : ℂ)⁻¹ * ∫ θ in (-π / 2)..(π / 2),
    Complex.exp (- (J : ℂ) * (wr + (θ : ℂ) * I)) *
      crossIdentity Δ_phi (wl - (θ : ℂ) * I) (wr + (θ : ℂ) * I)

/-- The universal large-spin limit `L_id(Δ_φ, w)` of the rescaled spin-`J`
Laplace transform `(2k)^(1 - 2Δ_φ) L_{2k}(w)` on `w ∈ UcDisk`. -/
noncomputable def universalLaplace (Δ_phi : ℝ) (w : ℂ) : ℂ :=
  ((2 * (4 : ℝ) ^ Δ_phi / Real.Gamma (2 * Δ_phi) : ℝ) : ℂ) * crossFactor Δ_phi w

/-- The real-valued universal large-spin Laplace transform `L_id(Δ_φ, σ)` for `σ < 0`:
`L_id(Δ_φ, σ) = (2 * 4^(2Δ_φ) / Γ(2Δ_φ)) * e^(Δ_φ σ) * (1 - e^σ)^(-2Δ_φ)`. -/
noncomputable def universalLaplaceReal (Δ_phi : ℝ) (σ : ℝ) : ℝ :=
  (2 * (4 : ℝ) ^ (2 * Δ_phi) / Real.Gamma (2 * Δ_phi)) *
    Real.exp (Δ_phi * σ) * (1 - Real.exp σ) ^ (- (2 * Δ_phi))

/-- The universal large-spin monomial spectral pairing for external dimension `Δ_phi`:
`(2 * 4^(2Δ_φ) / Γ(2Δ_φ)) ∑_{n=0}^∞ ((2Δ_φ)_n / n!) φ(Δ_φ + n)`. -/
noncomputable def universalMonomialPairing (Δ_phi : ℝ) (φ : ℝ → ℝ) : ℝ :=
  (2 * (4 : ℝ) ^ (2 * Δ_phi) / Real.Gamma (2 * Δ_phi)) *
    ∑' n : ℕ, (realPochhammer (2 * Δ_phi) n / (Nat.factorial n : ℝ)) * φ (Δ_phi + (n : ℝ))

lemma universalLaplaceReal_nonneg {Δ_phi σ : ℝ} (hΔ : 0 < Δ_phi) (hσ : σ < 0) :
    0 ≤ universalLaplaceReal Δ_phi σ := by
  dsimp [universalLaplaceReal]
  have h1 : 0 < Real.Gamma (2 * Δ_phi) := Real.Gamma_pos_of_pos (by positivity)
  have h2 : 0 < 1 - Real.exp σ := sub_pos.mpr (Real.exp_lt_one_iff.mpr hσ)
  positivity

/-- On the negative real axis `σ < 0`, `universalLaplace Δ_phi (σ : ℂ)` coincides with
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
  have hexp_cast :
      Complex.exp ((Δ_phi : ℂ) * (σ : ℂ)) = ((Real.exp (Δ_phi * σ) : ℝ) : ℂ) := by
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
  have h_cpow :
      DifferentiableAt ℂ (fun z => (1 - Complex.exp z) ^ (- (2 * Δ_phi : ℂ))) w :=
    h_sub.cpow_const (one_sub_exp_mem_slitPlane hw)
  exact ((h_exp.const_mul _).mul h_cpow).continuousAt.continuousWithinAt

/-- Continuity of the shifted `t`-channel identity contribution
`θ ↦ crossIdentity Δ_phi (w_l - iθ) (w_r + iθ)` on `ℝ`. -/
lemma continuous_crossIdentity_shift (Δ_phi : ℝ) {wl wr : ℂ}
    (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) :
    Continuous (fun θ : ℝ =>
      crossIdentity Δ_phi (wl - (θ : ℂ) * I) (wr + (θ : ℂ) * I)) := by
  have h1 : Continuous (fun θ : ℝ => crossFactor Δ_phi (wl - (θ : ℂ) * I)) :=
    (continuousOn_crossFactor Δ_phi).comp_continuous (by fun_prop)
      (fun θ => MonomialFourPointData.sub_I_mul_mem_UcDisk hwl θ)
  have h2 : Continuous (fun θ : ℝ => crossFactor Δ_phi (wr + (θ : ℂ) * I)) :=
    (continuousOn_crossFactor Δ_phi).comp_continuous (by fun_prop)
      (fun θ => MonomialFourPointData.add_I_mul_mem_UcDisk hwr θ)
  exact h1.mul h2

/-- Lower bound on `‖1 - e^(-ε + iθ)‖` for `0 < ε ≤ 1/2` and `θ ∈ [-π/2, π/2]`:
`e^(-1/2) / π * (ε + |θ|) ≤ ‖1 - e^(-ε + iθ)‖`. -/
lemma norm_one_sub_exp_ge_of_mem_Icc {ε θ : ℝ}
    (hε_pos : 0 < ε) (hε_le : ε ≤ 1 / 2) (hθ : θ ∈ Icc (-π / 2) (π / 2)) :
    Real.exp (-1 / 2) / π * (ε + |θ|) ≤
      ‖1 - Complex.exp ((-ε : ℂ) + (θ : ℂ) * I)‖ := by
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
      (Real.exp (-1 / 2) * (2 / π * ε) + Real.exp (-1 / 2) * (2 / π * |θ|)) / 2 := by
    ring
  linarith

/-- For `ε > 0` and `α ≠ -1`, the integral of `(ε + |θ|)^α` over `[-π/2, π/2]` is bounded for all
`0 < ε ≤ 1/2` by a constant times `ε^(α + 1) + 1`. -/
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
  · refine ⟨2 * (1 / 2 + π / 2) ^ (α + 1) / (α + 1), by positivity,
      fun {ε} hε_pos hε_le => ?_⟩
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

/-- Uniform bound on `∫_{-π/2}^{π/2} ‖1 - e^(-ε + iθ)‖^α dθ` for `0 < ε ≤ 1/2` and `α ≠ -1`. -/
lemma integral_norm_one_sub_exp_rpow_le {α : ℝ} (hα : α ≠ -1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 / 2 →
      (∫ θ in (-π / 2)..(π / 2),
        ‖1 - Complex.exp ((-ε : ℂ) + (θ : ℂ) * I)‖ ^ α) ≤
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
    have h_mono :
        (∫ θ in (-π / 2)..(π / 2),
          ‖1 - Complex.exp ((-ε : ℂ) + (θ : ℂ) * I)‖ ^ α) ≤
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
      (∫ θ in (-π / 2)..(π / 2),
        ‖1 - Complex.exp ((-ε : ℂ) + (θ : ℂ) * I)‖ ^ α)
        ≤ c ^ α * ∫ θ in (-π / 2)..(π / 2), (ε + |θ|) ^ α := h_mono
      _ ≤ c ^ α * (C0 * (ε ^ (α + 1) + 1)) :=
        mul_le_mul_of_nonneg_left (hC0 hε_pos hε_le) (by positivity)
      _ = (c ^ α * C0) * (ε ^ (α + 1) + 1) := by ring
  · refine ⟨π * (2 : ℝ) ^ α, by positivity, fun {ε} hε_pos _ => ?_⟩
    have h_mono :
        (∫ θ in (-π / 2)..(π / 2),
          ‖1 - Complex.exp ((-ε : ℂ) + (θ : ℂ) * I)‖ ^ α) ≤
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
      (∫ θ in (-π / 2)..(π / 2),
        ‖1 - Complex.exp ((-ε : ℂ) + (θ : ℂ) * I)‖ ^ α)
        ≤ π * (2 : ℝ) ^ α := h_mono
      _ ≤ (π * (2 : ℝ) ^ α) * (ε ^ (α + 1) + 1) := by
        nlinarith [show 0 ≤ π * (2 : ℝ) ^ α by positivity]

/-- The binomial series coefficient `(a)_n / n! = choose(a + n - 1, n)`. -/
noncomputable def pochhammerCoeff (a : ℝ) (n : ℕ) : ℝ :=
  realPochhammer a n / (Nat.factorial n : ℝ)

lemma pochhammerCoeff_nonneg {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    0 ≤ pochhammerCoeff a n := by
  dsimp [pochhammerCoeff]
  exact div_nonneg (realPochhammer_nonneg ha n) (Nat.cast_nonneg _)

/-- The exact finite-spin `t`-channel identity Laplace transform on the negative real axis `σ < 0`
at spin `K ∈ ℕ`:
`identityLaplaceReal(Δ_φ, K, σ) =`
`2 * 4^(2Δ_φ) * e^(Δ_φ σ) * ∑_{n=0}^∞ ((2Δ_φ)_n / n!) ((2Δ_φ)_{n + K} / (n + K)!) e^(n σ)`.
Including the exact finite-spin binomial coefficients `((2Δ_φ)_{n + K} / (n + K)!)` retains all
`1 / K^m` subleading `t`-channel identity corrections. -/
noncomputable def identityLaplaceReal (Δ_phi : ℝ) (K : ℕ) (σ : ℝ) : ℝ :=
  2 * (4 : ℝ) ^ (2 * Δ_phi) * Real.exp (Δ_phi * σ) *
    ∑' n : ℕ, pochhammerCoeff (2 * Δ_phi) n * pochhammerCoeff (2 * Δ_phi) (n + K) *
      (Real.exp σ) ^ n

/-- The exact finite-spin `t`-channel identity monomial spectral pairing at spin `K ∈ ℕ`:
`identityMonomialPairing(Δ_φ, K, φ) =`
`2 * 4^(2Δ_φ) ∑_{n=0}^∞ ((2Δ_φ)_n / n!) ((2Δ_φ)_{n + K} / (n + K)!) φ(Δ_φ + n)`. -/
noncomputable def identityMonomialPairing (Δ_phi : ℝ) (K : ℕ) (φ : ℝ → ℝ) : ℝ :=
  2 * (4 : ℝ) ^ (2 * Δ_phi) *
    ∑' n : ℕ, pochhammerCoeff (2 * Δ_phi) n * pochhammerCoeff (2 * Δ_phi) (n + K) *
      φ (Δ_phi + (n : ℝ))

lemma identityLaplaceReal_nonneg {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) (K : ℕ) (σ : ℝ) :
    0 ≤ identityLaplaceReal Δ_phi K σ := by
  dsimp [identityLaplaceReal]
  refine mul_nonneg (by positivity) (tsum_nonneg fun n => ?_)
  exact mul_nonneg
    (mul_nonneg (pochhammerCoeff_nonneg (by positivity) n)
      (pochhammerCoeff_nonneg (by positivity) (n + K)))
    (by positivity)

lemma ringChoose_add_sub_one_eq_pochhammerCoeff (a : ℝ) (n : ℕ) :
    Ring.choose (a + (n : ℝ) - 1) n = pochhammerCoeff a n := by
  have h1 := Ring.factorial_nsmul_multichoose_eq_ascPochhammer a n
  rw [Ring.multichoose_eq, Polynomial.ascPochhammer_smeval_eq_eval, nsmul_eq_mul] at h1
  have hne : (Nat.factorial n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  exact eq_div_of_mul_eq hne (by rw [mul_comm, h1]; rfl)

/-- Real binomial series expansion of `(1 - x)^(-a)` for `|x| < 1`. -/
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

/-- Complex binomial series expansion of `(1 - z)^(-a)` for `‖z‖ < 1`. -/
lemma hasSum_one_sub_cpow_neg (a : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (pochhammerCoeff a n : ℂ) * z ^ n) ((1 - z) ^ (- (a : ℂ))) := by
  have hz_eball : z ∈ Metric.eball (0 : ℂ) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa using hz
  have h_fp :=
    (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero (a : ℂ)).hasSum hz_eball
  rw [FormalMultilinearSeries.ofScalars_apply_eq', zero_add, one_div,
    ← Complex.cpow_neg] at h_fp
  refine h_fp.congr_fun fun n => ?_
  rw [smul_eq_mul]
  congr 1
  have h_cast : (a : ℂ) + (n : ℂ) - 1 = ((a + (n : ℝ) - 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [h_cast, ← Complex.ofReal_choose, ringChoose_add_sub_one_eq_pochhammerCoeff]

/-- Binomial series expansion of `e^(Δ_φ σ) (1 - e^σ)^(-2Δ_φ)` for `σ < 0`. -/
lemma hasSum_exp_mul_one_sub_exp_rpow_neg (Δ_phi : ℝ) {σ : ℝ} (hσ : σ < 0) :
    HasSum
      (fun n : ℕ => pochhammerCoeff (2 * Δ_phi) n * Real.exp ((Δ_phi + (n : ℝ)) * σ))
      (Real.exp (Δ_phi * σ) * (1 - Real.exp σ) ^ (- (2 * Δ_phi))) := by
  have h_abs : |Real.exp σ| < 1 := by
    rw [abs_of_pos (Real.exp_pos σ)]
    exact Real.exp_lt_one_iff.mpr hσ
  have h_sum :=
    (hasSum_one_sub_rpow_neg (2 * Δ_phi) h_abs).mul_left (Real.exp (Δ_phi * σ))
  refine h_sum.congr_fun fun n => ?_
  rw [← mul_left_comm, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 2
  ring

/-- Binomial series expansion of `e^(Δ_φ w) (1 - e^w)^(-2Δ_φ)` on `w ∈ UcDisk`. -/
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

@[simp]
lemma pochhammerCoeff_zero (a : ℝ) : pochhammerCoeff a 0 = 1 := by
  simp [pochhammerCoeff]

lemma pochhammerCoeff_succ (a : ℝ) (n : ℕ) :
    pochhammerCoeff a (n + 1) =
      pochhammerCoeff a n * ((a + (n : ℝ)) / ((n : ℝ) + 1)) := by
  dsimp [pochhammerCoeff]
  rw [realPochhammer_succ, Nat.factorial_succ]
  push_cast
  rw [div_mul_div_comm, mul_comm ((n : ℝ) + 1)]

lemma prod_range_add_eq_realPochhammer (a : ℝ) (n : ℕ) :
    (∏ j ∈ Finset.range n, (a + (j : ℝ))) = realPochhammer a n := by
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.prod_range_succ, ih, realPochhammer_succ]

/-- Euler's Gamma limit for binomial coefficients: for `a > 0`,
`lim_{M → ∞} M^(1 - a) (a)_M / M! = 1 / Γ(a)`. -/
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

/-!
## 2. Quantitative `O(K⁻¹)` Euler Gamma Limit and Binomial Series Bound
-/

lemma hasDerivAt_one_add_rpow (p : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun y : ℝ => (1 + y) ^ p) (p * (1 + t) ^ (p - 1)) t := by
  have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 t := (hasDerivAt_id t).const_add 1
  have hpos : 0 < 1 + t := by linarith
  simpa [mul_one] using h1.rpow_const (Or.inl hpos.ne')

lemma abs_one_add_rpow_neg_sub_one_le {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    |(1 + x) ^ (-a) - 1| ≤ a * x := by
  have h0 : (0 : ℝ) ∈ Icc 0 x := ⟨le_rfl, hx⟩
  have hx_mem : x ∈ Icc 0 x := ⟨hx, le_rfl⟩
  have hstep := (convex_Icc 0 x).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun y : ℝ => (1 + y) ^ (-a))
    (f' := fun y : ℝ => (-a) * (1 + y) ^ (-a - 1))
    (C := a)
    (fun y (hy : y ∈ Icc 0 x) => (hasDerivAt_one_add_rpow (-a) hy.1).hasDerivWithinAt)
    (fun y (hy : y ∈ Icc 0 x) => ?_) h0 hx_mem
  · simpa [Real.norm_eq_abs, abs_of_nonneg hx] using hstep
  · rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos ha]
    have hpos : 0 < 1 + y := by linarith [hy.1]
    rw [abs_of_pos (Real.rpow_pos_of_pos hpos _)]
    have hle1 : (1 + y) ^ (-a - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hy.1]) (by linarith)
    linarith [mul_le_mul_of_nonneg_left hle1 ha.le]

lemma abs_one_add_rpow_one_sub_mul_sub_le {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    |(1 + x) ^ (1 - a) * (1 + a * x) - (1 + x)| ≤ (a + |a * (2 - a)|) * x ^ 2 := by
  have h0 : (0 : ℝ) ∈ Icc 0 x := ⟨le_rfl, hx⟩
  have hx_mem : x ∈ Icc 0 x := ⟨hx, le_rfl⟩
  let g : ℝ → ℝ := fun y => (1 + y) ^ (1 - a) * (1 + a * y) - (1 + y)
  let g' : ℝ → ℝ := fun y => ((1 + y) ^ (-a) - 1) + a * (2 - a) * y * (1 + y) ^ (-a)
  have hg_deriv : ∀ y ∈ Icc 0 x, HasDerivWithinAt g (g' y) (Icc 0 x) y := by
    intro y hy
    have hpos : 0 < 1 + y := by linarith [hy.1]
    have h1 := hasDerivAt_one_add_rpow (1 - a) hy.1
    have h2 : HasDerivAt (fun z : ℝ => 1 + a * z) a y := by
      simpa using ((hasDerivAt_id y).const_mul a).const_add 1
    have h3 : HasDerivAt (fun z : ℝ => 1 + z) 1 y := (hasDerivAt_id y).const_add 1
    have h4 := (h1.mul h2).sub h3
    refine h4.hasDerivWithinAt.congr_deriv ?_
    have hrpow : (1 + y) ^ (1 - a) = (1 + y) ^ (-a) * (1 + y) := by
      have : 1 - a = -a + 1 := by ring
      rw [this, Real.rpow_add hpos, Real.rpow_one]
    have hsub : 1 - a - 1 = -a := by ring
    dsimp [g']
    rw [hsub, hrpow]
    ring
  have hg'_bound : ∀ y ∈ Icc 0 x, ‖g' y‖ ≤ (a + |a * (2 - a)|) * x := by
    intro y hy
    rw [Real.norm_eq_abs]
    dsimp [g']
    have h1 : |(1 + y) ^ (-a) - 1| ≤ a * x :=
      (abs_one_add_rpow_neg_sub_one_le ha hy.1).trans
        (mul_le_mul_of_nonneg_left hy.2 ha.le)
    have hpos : 0 < 1 + y := by linarith [hy.1]
    have hrpow_le : (1 + y) ^ (-a) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hy.1]) (by linarith)
    have h2 : |a * (2 - a) * y * (1 + y) ^ (-a)| ≤ |a * (2 - a)| * x := by
      rw [abs_mul, abs_mul, abs_of_nonneg hy.1,
        abs_of_pos (Real.rpow_pos_of_pos hpos _)]
      calc
        |a * (2 - a)| * y * (1 + y) ^ (-a)
          ≤ |a * (2 - a)| * x * 1 :=
            mul_le_mul
              (mul_le_mul_of_nonneg_left hy.2 (abs_nonneg _))
              hrpow_le (Real.rpow_pos_of_pos hpos _).le (by positivity)
        _ = |a * (2 - a)| * x := mul_one _
    calc
      |((1 + y) ^ (-a) - 1) + a * (2 - a) * y * (1 + y) ^ (-a)|
        ≤ |(1 + y) ^ (-a) - 1| + |a * (2 - a) * y * (1 + y) ^ (-a)| := abs_add_le _ _
      _ ≤ a * x + |a * (2 - a)| * x := add_le_add h1 h2
      _ = (a + |a * (2 - a)|) * x := by ring
  have hstep :=
    (convex_Icc 0 x).norm_image_sub_le_of_norm_hasDerivWithin_le hg_deriv hg'_bound h0 hx_mem
  have hg0 : g 0 = 0 := by dsimp [g]; simp
  rw [hg0, sub_zero, Real.norm_eq_abs, sub_zero, Real.norm_eq_abs, abs_of_nonneg hx] at hstep
  calc
    |g x| ≤ (a + |a * (2 - a)|) * x * x := hstep
    _ = (a + |a * (2 - a)|) * x ^ 2 := by ring

lemma exists_bound_rpow_mul_pochhammerCoeff {a : ℝ} (ha : 0 < a) :
    ∃ B : ℝ, 0 < B ∧ ∀ M : ℕ, (M : ℝ) ^ (1 - a) * pochhammerCoeff a M ≤ B := by
  let u : ℕ → ℝ := fun M => (M : ℝ) ^ (1 - a) * pochhammerCoeff a M
  have h_lim := tendsto_rpow_mul_pochhammerCoeff ha
  have h_ev : ∀ᶠ M : ℕ in atTop, u M < (Real.Gamma a)⁻¹ + 1 :=
    h_lim.eventually (gt_mem_nhds (by linarith))
  rw [Filter.eventually_atTop] at h_ev
  rcases h_ev with ⟨M₀, hM₀⟩
  let S : Finset ℝ := (Finset.range (M₀ + 1)).image u
  have hS_ne : S.Nonempty := by
    refine Finset.Nonempty.image ?_ u
    exact ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ M₀)⟩
  let B := max ((Real.Gamma a)⁻¹ + 1) (S.max' hS_ne)
  have hB_pos : 0 < B := by
    have : 0 < (Real.Gamma a)⁻¹ + 1 := by
      have := Real.Gamma_pos_of_pos ha
      positivity
    exact lt_of_lt_of_le this (le_max_left _ _)
  refine ⟨B, hB_pos, fun M => ?_⟩
  rcases le_or_gt M M₀ with hle | hgt
  · have hmem : u M ∈ S :=
      Finset.mem_image_of_mem u (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
    exact (Finset.le_max' S (u M) hmem).trans (le_max_right _ _)
  · exact (hM₀ M hgt.le).le.trans (le_max_left _ _)

/-- **Quantitative `O(M⁻¹)` Rate for Euler's Gamma Limit**:
For `a > 0`, there exists `C ≥ 0` such that for all `M ≥ 1`,
`|M^(1 - a) (a)_M / M! - (Γ(a))⁻¹| ≤ C / M`. -/
theorem exists_abs_rpow_mul_pochhammerCoeff_sub_inv_gamma_le {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {M : ℕ}, 1 ≤ M →
      |(M : ℝ) ^ (1 - a) * pochhammerCoeff a M - (Real.Gamma a)⁻¹| ≤ C / (M : ℝ) := by
  let u : ℕ → ℝ := fun M => (M : ℝ) ^ (1 - a) * pochhammerCoeff a M
  obtain ⟨B, hB_pos, hB⟩ := exists_bound_rpow_mul_pochhammerCoeff ha
  let C : ℝ := B * (a + |a * (2 - a)|)
  have hC_nonneg : 0 ≤ C := by dsimp [C]; positivity
  have h_step_one : ∀ {m : ℕ}, 1 ≤ m →
      |u (m + 1) - u m| ≤ C * (1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ)) := by
    intro m hm
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hm1_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    let x : ℝ := 1 / (m : ℝ)
    have hx_nonneg : 0 ≤ x := by positivity
    have h1x_pos : 0 < 1 + x := by positivity
    have h_u_succ : u (m + 1) = u m * ((1 + x) ^ (1 - a) * (1 + a * x) / (1 + x)) := by
      dsimp [u, x]
      rw [pochhammerCoeff_succ]
      have h_m1 : ((m + 1 : ℕ) : ℝ) = (m : ℝ) * (1 + 1 / (m : ℝ)) := by
        push_cast; field_simp
      have h_am : (a + (m : ℝ)) / ((m : ℝ) + 1) =
          (1 + a * (1 / (m : ℝ))) / (1 + 1 / (m : ℝ)) := by
        field_simp; ring
      rw [h_m1, Real.mul_rpow hm_pos.le (by positivity), h_am]
      ring
    have h_diff : u (m + 1) - u m =
        u m * (((1 + x) ^ (1 - a) * (1 + a * x) - (1 + x)) / (1 + x)) := by
      rw [h_u_succ]
      have : (1 + x) ≠ 0 := h1x_pos.ne'
      field_simp
    have hu_nonneg : 0 ≤ u m :=
      mul_nonneg (by positivity) (pochhammerCoeff_nonneg ha.le m)
    rw [h_diff, abs_mul, abs_of_nonneg hu_nonneg, abs_div, abs_of_pos h1x_pos]
    have h_g := abs_one_add_rpow_one_sub_mul_sub_le ha hx_nonneg
    have h_x2_div : x ^ 2 / (1 + x) = 1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ) := by
      dsimp [x]
      push_cast
      field_simp
      ring
    calc
      u m * (|(1 + x) ^ (1 - a) * (1 + a * x) - (1 + x)| / (1 + x))
        ≤ B * (((a + |a * (2 - a)|) * x ^ 2) / (1 + x)) := by
          refine mul_le_mul (hB m)
            (div_le_div_of_nonneg_right h_g h1x_pos.le) (by positivity) hB_pos.le
      _ = C * (x ^ 2 / (1 + x)) := by dsimp [C]; ring
      _ = C * (1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ)) := by rw [h_x2_div]
  have h_tele : ∀ {M : ℕ}, 1 ≤ M → ∀ N : ℕ,
      |u (M + N) - u M| ≤ C * (1 / (M : ℝ) - 1 / ((M + N : ℕ) : ℝ)) := by
    intro M hM N
    induction N with
    | zero => simp
    | succ N ih =>
      have hMN : 1 ≤ M + N := by omega
      have h1 := h_step_one hMN
      have h_add : M + (N + 1) = (M + N) + 1 := by omega
      rw [h_add]
      calc
        |u (M + N + 1) - u M|
          = |(u (M + N + 1) - u (M + N)) + (u (M + N) - u M)| := by ring_nf
        _ ≤ |u (M + N + 1) - u (M + N)| + |u (M + N) - u M| := abs_add_le _ _
        _ ≤ C * (1 / ((M + N : ℕ) : ℝ) - 1 / ((M + N + 1 : ℕ) : ℝ)) +
            C * (1 / (M : ℝ) - 1 / ((M + N : ℕ) : ℝ)) := add_le_add h1 ih
        _ = C * (1 / (M : ℝ) - 1 / ((M + N + 1 : ℕ) : ℝ)) := by ring
  refine ⟨C, hC_nonneg, fun {M} hM => ?_⟩
  have h_lim_N : Tendsto (fun N : ℕ => |u (M + N) - u M|) atTop
      (𝓝 |(Real.Gamma a)⁻¹ - u M|) := by
    have h1 : Tendsto (fun N : ℕ => u (M + N)) atTop (𝓝 (Real.Gamma a)⁻¹) := by
      have hc := (tendsto_rpow_mul_pochhammerCoeff ha).comp (tendsto_add_atTop_nat M)
      refine hc.congr fun N => ?_
      dsimp [Function.comp_def]
      rw [add_comm N M]
    exact (h1.sub tendsto_const_nhds).abs
  rw [abs_sub_comm]
  refine le_of_tendsto' h_lim_N (fun N => ?_)
  have h_le := h_tele hM N
  have h_pos : 0 ≤ 1 / ((M + N : ℕ) : ℝ) := by positivity
  calc
    |u (M + N) - u M| ≤ C * (1 / (M : ℝ) - 1 / ((M + N : ℕ) : ℝ)) := h_le
    _ ≤ C * (1 / (M : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) hC_nonneg
    _ = C / (M : ℝ) := mul_one_div C (M : ℝ)

lemma abs_one_add_div_rpow_sub_one_le (b : ℝ) (n : ℕ) {K : ℝ} (hK : 1 ≤ K) :
    |(1 + (n : ℝ) / K) ^ b - 1| ≤
      |b| * (1 + (n : ℝ)) ^ (⌈|b - 1|⌉₊ + 1) / K := by
  have hK_pos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  let x : ℝ := (n : ℝ) / K
  have hx_nonneg : 0 ≤ x := by positivity
  have hx_le : x ≤ (n : ℝ) := div_le_self (Nat.cast_nonneg n) hK
  let m : ℕ := ⌈|b - 1|⌉₊
  have h0 : (0 : ℝ) ∈ Icc 0 x := ⟨le_rfl, hx_nonneg⟩
  have hx_mem : x ∈ Icc 0 x := ⟨hx_nonneg, le_rfl⟩
  have h_deriv_bd : ∀ y ∈ Icc 0 x,
      ‖b * (1 + y) ^ (b - 1)‖ ≤ |b| * (1 + (n : ℝ)) ^ m := by
    intro y hy
    rw [Real.norm_eq_abs, abs_mul]
    have h1y : 1 ≤ 1 + y := by linarith [hy.1]
    have hpos : 0 < 1 + y := by linarith [hy.1]
    rw [abs_of_pos (Real.rpow_pos_of_pos hpos _)]
    have hm_ge : b - 1 ≤ (m : ℝ) :=
      (le_abs_self (b - 1)).trans (Nat.le_ceil |b - 1|)
    have hrpow1 : (1 + y) ^ (b - 1) ≤ (1 + y) ^ (m : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h1y hm_ge
    rw [Real.rpow_natCast] at hrpow1
    have hrpow2 : (1 + y) ^ m ≤ (1 + (n : ℝ)) ^ m :=
      pow_le_pow_left₀ hpos.le (by linarith [hy.2, hx_le]) m
    exact mul_le_mul_of_nonneg_left (hrpow1.trans hrpow2) (abs_nonneg b)
  have hstep := (convex_Icc 0 x).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun y : ℝ => (1 + y) ^ b)
    (f' := fun y : ℝ => b * (1 + y) ^ (b - 1))
    (fun y (hy : y ∈ Icc 0 x) => (hasDerivAt_one_add_rpow b hy.1).hasDerivWithinAt)
    h_deriv_bd h0 hx_mem
  simp only [add_zero, Real.one_rpow, Real.norm_eq_abs, sub_zero,
    abs_of_nonneg hx_nonneg] at hstep
  have hn_le : (n : ℝ) ≤ 1 + (n : ℝ) := by linarith
  have h_coeff_nonneg : 0 ≤ |b| * (1 + (n : ℝ)) ^ m :=
    mul_nonneg (abs_nonneg b) (pow_nonneg (by positivity) m)
  calc
    |(1 + x) ^ b - 1|
      ≤ (|b| * (1 + (n : ℝ)) ^ m) * ((n : ℝ) / K) := hstep
    _ ≤ (|b| * (1 + (n : ℝ)) ^ m) * ((1 + (n : ℝ)) / K) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hn_le hK_pos.le) h_coeff_nonneg
    _ = |b| * (1 + (n : ℝ)) ^ (m + 1) / K := by
      rw [pow_succ]
      ring

lemma one_add_natCast_pow_mul_exp_le (p : ℕ) {σ_plus σ : ℝ}
    (hσ_plus : σ_plus < 0) (hσ : σ ≤ σ_plus) (n : ℕ) :
    (1 + (n : ℝ)) ^ p * (Real.exp σ) ^ n ≤
      (1 + (-(σ_plus) / (2 * ((p : ℝ) + 1)))⁻¹) ^ p *
        (Real.exp (σ_plus / 2)) ^ n := by
  let c : ℝ := -(σ_plus) / (2 * ((p : ℝ) + 1))
  have h_neg_pos : 0 < -σ_plus := neg_pos.mpr hσ_plus
  have hc_pos : 0 < c := by dsimp [c]; positivity
  have h_base : 1 + (n : ℝ) ≤ (1 + c⁻¹) * Real.exp (c * (n : ℝ)) := by
    have h1 : 1 + (n : ℝ) ≤ (1 + c⁻¹) * (1 + c * (n : ℝ)) := by
      have h_id : (1 + c⁻¹) * (1 + c * (n : ℝ)) =
          1 + (n : ℝ) + (c⁻¹ + c * (n : ℝ)) := by
        have hc_ne : c ≠ 0 := hc_pos.ne'
        field_simp
        ring
      rw [h_id]
      linarith [show 0 ≤ c⁻¹ + c * (n : ℝ) by positivity]
    have h2 : 1 + c * (n : ℝ) ≤ Real.exp (c * (n : ℝ)) := by
      linarith [Real.add_one_le_exp (c * (n : ℝ))]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  have h_pow : (1 + (n : ℝ)) ^ p ≤
      (1 + c⁻¹) ^ p * (Real.exp ((p : ℝ) * c)) ^ n := by
    calc
      (1 + (n : ℝ)) ^ p
        ≤ ((1 + c⁻¹) * Real.exp (c * (n : ℝ))) ^ p :=
          pow_le_pow_left₀ (by positivity) h_base p
      _ = (1 + c⁻¹) ^ p * (Real.exp (c * (n : ℝ))) ^ p := mul_pow _ _ _
      _ = (1 + c⁻¹) ^ p * (Real.exp ((p : ℝ) * c)) ^ n := by
          congr 1
          rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
          congr 1
          ring
  have h_pc_le : (p : ℝ) * c ≤ -σ_plus / 2 := by
    dsimp [c]
    have hp_le : (p : ℝ) ≤ (p : ℝ) + 1 := by linarith
    have h_alg :
        (p : ℝ) * (-σ_plus / (2 * ((p : ℝ) + 1))) =
          (-σ_plus / 2) * ((p : ℝ) / ((p : ℝ) + 1)) := by
      have : (p : ℝ) + 1 ≠ 0 := by positivity
      field_simp
    rw [h_alg]
    calc
      (-σ_plus / 2) * ((p : ℝ) / ((p : ℝ) + 1))
        ≤ (-σ_plus / 2) * 1 :=
          mul_le_mul_of_nonneg_left
            ((div_le_one (by positivity)).mpr hp_le) (by linarith)
      _ = -σ_plus / 2 := mul_one _
  have h_exp_prod :
      (Real.exp ((p : ℝ) * c)) ^ n * (Real.exp σ) ^ n ≤
        (Real.exp (σ_plus / 2)) ^ n := by
    rw [← mul_pow, ← Real.exp_add]
    exact pow_le_pow_left₀ (by positivity)
      (Real.exp_le_exp.mpr (by linarith)) n
  calc
    (1 + (n : ℝ)) ^ p * (Real.exp σ) ^ n
      ≤ ((1 + c⁻¹) ^ p * (Real.exp ((p : ℝ) * c)) ^ n) * (Real.exp σ) ^ n :=
        mul_le_mul_of_nonneg_right h_pow (by positivity)
    _ = (1 + c⁻¹) ^ p * ((Real.exp ((p : ℝ) * c)) ^ n * (Real.exp σ) ^ n) := by
        ring
    _ ≤ (1 + c⁻¹) ^ p * (Real.exp (σ_plus / 2)) ^ n :=
        mul_le_mul_of_nonneg_left h_exp_prod (by positivity)

/-- **Uniform `O(K⁻¹)` Bound for the Shifted Binomial Series**:
For `a > 0` and `σ_plus < 0`, there exists `C ≥ 0` such that for all `K ≥ 1` and all
`σ ≤ σ_plus`,
`|K^(1 - a) ∑_{n=0}^∞ ((a)_n / n!) ((a)_{n + K} / (n + K)!) e^(n σ) - (Γ(a))⁻¹ (1 - e^σ)^(-a)|`
`≤ C / K`. -/
theorem exists_uniform_bound_tsum_pochhammerCoeff_sub {a σ_plus : ℝ}
    (ha : 0 < a) (hσ_plus : σ_plus < 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : ℕ}, 1 ≤ K → ∀ {σ : ℝ}, σ ≤ σ_plus →
      |(K : ℝ) ^ (1 - a) *
          (∑' n : ℕ, pochhammerCoeff a n * pochhammerCoeff a (n + K) *
            (Real.exp σ) ^ n) -
        (Real.Gamma a)⁻¹ * (1 - Real.exp σ) ^ (-a)| ≤ C / (K : ℝ) := by
  obtain ⟨B, hB_pos, hB⟩ := exists_bound_rpow_mul_pochhammerCoeff ha
  obtain ⟨C₀, hC₀_nonneg, hC₀⟩ := exists_abs_rpow_mul_pochhammerCoeff_sub_inv_gamma_le ha
  set p : ℕ := ⌈|(a - 1) - 1|⌉₊ + 1
  have h_neg_pos : 0 < -σ_plus := neg_pos.mpr hσ_plus
  set A_p : ℝ := (1 + (-(σ_plus) / (2 * ((p : ℝ) + 1)))⁻¹) ^ p
  have hAp_nonneg : 0 ≤ A_p := pow_nonneg (by positivity) p
  set q := Real.exp (σ_plus / 2)
  have hq_pos : 0 < q := Real.exp_pos _
  have hq_lt1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hq_abs : |q| < 1 := by rw [abs_of_pos hq_pos]; exact hq_lt1
  have h_sum_q := hasSum_one_sub_rpow_neg a hq_abs
  set C_tot : ℝ := (C₀ + B * |a - 1| * A_p) * (1 - q) ^ (-a)
  have h_coeff_nonneg : 0 ≤ C₀ + B * |a - 1| * A_p :=
    add_nonneg hC₀_nonneg (mul_nonneg (mul_nonneg hB_pos.le (abs_nonneg _)) hAp_nonneg)
  have hC_tot_nonneg : 0 ≤ C_tot :=
    mul_nonneg h_coeff_nonneg (Real.rpow_pos_of_pos (by linarith) _).le
  refine ⟨C_tot, hC_tot_nonneg, fun {K} hK {σ} hσ => ?_⟩
  have hK_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hK_ge1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hσ_neg : σ < 0 := lt_of_le_of_lt hσ hσ_plus
  have h_exp_abs : |Real.exp σ| < 1 := by
    rw [abs_of_pos (Real.exp_pos σ)]; exact Real.exp_lt_one_iff.mpr hσ_neg
  have h_sum_σ := hasSum_one_sub_rpow_neg a h_exp_abs
  set term1 : ℕ → ℝ := fun n =>
    (K : ℝ) ^ (1 - a) * (pochhammerCoeff a n * pochhammerCoeff a (n + K) * (Real.exp σ) ^ n)
  set term2 : ℕ → ℝ := fun n =>
    (Real.Gamma a)⁻¹ * (pochhammerCoeff a n * (Real.exp σ) ^ n)
  set dom : ℕ → ℝ := fun n =>
    ((C₀ + B * |a - 1| * A_p) / (K : ℝ)) * (pochhammerCoeff a n * q ^ n)
  have h_pt : ∀ n : ℕ, |term1 n - term2 n| ≤ dom n := by
    intro n
    have h_diff_coeff :
        |(K : ℝ) ^ (1 - a) * pochhammerCoeff a (n + K) - (Real.Gamma a)⁻¹| ≤
          (C₀ + B * |a - 1| * (1 + (n : ℝ)) ^ p) / (K : ℝ) := by
      let u_nK := ((n + K : ℕ) : ℝ) ^ (1 - a) * pochhammerCoeff a (n + K)
      have h_id : (K : ℝ) ^ (1 - a) * pochhammerCoeff a (n + K) =
          u_nK * (1 + (n : ℝ) / (K : ℝ)) ^ (a - 1) := by
        dsimp [u_nK]
        have h_cast : ((n + K : ℕ) : ℝ) = (K : ℝ) * (1 + (n : ℝ) / (K : ℝ)) := by
          push_cast; field_simp; ring
        have hpos_r : 0 < 1 + (n : ℝ) / (K : ℝ) := by positivity
        rw [h_cast, Real.mul_rpow hK_pos.le hpos_r.le]
        have h_canc :
            (1 + (n : ℝ) / (K : ℝ)) ^ (1 - a) * (1 + (n : ℝ) / (K : ℝ)) ^ (a - 1) = 1 := by
          rw [← Real.rpow_add hpos_r, sub_add_sub_cancel, sub_self, Real.rpow_zero]
        calc
          (K : ℝ) ^ (1 - a) * pochhammerCoeff a (n + K)
            = (K : ℝ) ^ (1 - a) * pochhammerCoeff a (n + K) *
                ((1 + (n : ℝ) / (K : ℝ)) ^ (1 - a) *
                  (1 + (n : ℝ) / (K : ℝ)) ^ (a - 1)) := by rw [h_canc, mul_one]
          _ = (K : ℝ) ^ (1 - a) * (1 + (n : ℝ) / (K : ℝ)) ^ (1 - a) *
                pochhammerCoeff a (n + K) * (1 + (n : ℝ) / (K : ℝ)) ^ (a - 1) := by ring
      rw [h_id]
      have hu_nonneg : 0 ≤ u_nK :=
        mul_nonneg (by positivity) (pochhammerCoeff_nonneg ha.le (n + K))
      have h_b1 : |u_nK - (Real.Gamma a)⁻¹| ≤ C₀ / (K : ℝ) := by
        have hnK : 1 ≤ n + K := by omega
        have hnK_ge : (K : ℝ) ≤ ((n + K : ℕ) : ℝ) := by exact_mod_cast (by omega : K ≤ n + K)
        exact (hC₀ hnK).trans (div_le_div_of_nonneg_left hC₀_nonneg hK_pos hnK_ge)
      have h_b2 := abs_one_add_div_rpow_sub_one_le (a - 1) n hK_ge1
      calc
        |u_nK * (1 + (n : ℝ) / (K : ℝ)) ^ (a - 1) - (Real.Gamma a)⁻¹|
          = |(u_nK - (Real.Gamma a)⁻¹) +
              u_nK * ((1 + (n : ℝ) / (K : ℝ)) ^ (a - 1) - 1)| := by ring_nf
        _ ≤ |u_nK - (Real.Gamma a)⁻¹| +
              |u_nK * ((1 + (n : ℝ) / (K : ℝ)) ^ (a - 1) - 1)| := abs_add_le _ _
        _ = |u_nK - (Real.Gamma a)⁻¹| +
              u_nK * |(1 + (n : ℝ) / (K : ℝ)) ^ (a - 1) - 1| := by
            rw [abs_mul, abs_of_nonneg hu_nonneg]
        _ ≤ C₀ / (K : ℝ) +
              B * (|a - 1| * (1 + (n : ℝ)) ^ p / (K : ℝ)) :=
            add_le_add h_b1
              (mul_le_mul (hB (n + K)) h_b2 (abs_nonneg _) hB_pos.le)
        _ = (C₀ + B * |a - 1| * (1 + (n : ℝ)) ^ p) / (K : ℝ) := by ring
    have h_factor : term1 n - term2 n =
        ((K : ℝ) ^ (1 - a) * pochhammerCoeff a (n + K) - (Real.Gamma a)⁻¹) *
          (pochhammerCoeff a n * (Real.exp σ) ^ n) := by
      dsimp [term1, term2]; ring
    rw [h_factor, abs_mul,
      abs_of_nonneg (mul_nonneg (pochhammerCoeff_nonneg ha.le n) (by positivity))]
    have h_exp_le_q : (Real.exp σ) ^ n ≤ q ^ n :=
      pow_le_pow_left₀ (by positivity)
        (Real.exp_le_exp.mpr (by linarith)) n
    have h_pow_exp := one_add_natCast_pow_mul_exp_le p hσ_plus hσ n
    calc
      |(K : ℝ) ^ (1 - a) * pochhammerCoeff a (n + K) - (Real.Gamma a)⁻¹| *
          (pochhammerCoeff a n * (Real.exp σ) ^ n)
        ≤ ((C₀ + B * |a - 1| * (1 + (n : ℝ)) ^ p) / (K : ℝ)) *
            (pochhammerCoeff a n * (Real.exp σ) ^ n) :=
          mul_le_mul_of_nonneg_right h_diff_coeff
            (mul_nonneg (pochhammerCoeff_nonneg ha.le n) (by positivity))
      _ = (pochhammerCoeff a n / (K : ℝ)) *
            (C₀ * (Real.exp σ) ^ n +
              B * |a - 1| * ((1 + (n : ℝ)) ^ p * (Real.exp σ) ^ n)) := by ring
      _ ≤ (pochhammerCoeff a n / (K : ℝ)) *
            (C₀ * q ^ n + B * |a - 1| * (A_p * q ^ n)) := by
          refine mul_le_mul_of_nonneg_left
            (add_le_add
              (mul_le_mul_of_nonneg_left h_exp_le_q hC₀_nonneg)
              (mul_le_mul_of_nonneg_left h_pow_exp (by positivity)))
            (div_nonneg (pochhammerCoeff_nonneg ha.le n) hK_pos.le)
      _ = dom n := by dsimp [dom]; ring
  have h_sum_dom : HasSum dom (C_tot / (K : ℝ)) := by
    have h1 := h_sum_q.mul_left ((C₀ + B * |a - 1| * A_p) / (K : ℝ))
    have h_eq : ((C₀ + B * |a - 1| * A_p) / (K : ℝ)) * (1 - q) ^ (-a) =
        C_tot / (K : ℝ) := by dsimp [C_tot]; ring
    rwa [h_eq] at h1
  have h_sum1 : Summable term1 := by
    have h_sub : Summable (fun n => term1 n - term2 n) :=
      Summable.of_norm_bounded h_sum_dom.summable
        (fun n => by rw [Real.norm_eq_abs]; exact h_pt n)
    have h_s2 : Summable term2 := (h_sum_σ.mul_left (Real.Gamma a)⁻¹).summable
    have h_add := h_sub.add h_s2
    refine h_add.congr (fun n => by ring)
  have h_tsum1 :
      (K : ℝ) ^ (1 - a) *
        (∑' n : ℕ, pochhammerCoeff a n * pochhammerCoeff a (n + K) * (Real.exp σ) ^ n) =
        ∑' n : ℕ, term1 n := by
    dsimp [term1]
    rw [tsum_mul_left]
  have h_tsum2 : (Real.Gamma a)⁻¹ * (1 - Real.exp σ) ^ (-a) = ∑' n : ℕ, term2 n :=
    ((h_sum_σ.mul_left (Real.Gamma a)⁻¹).tsum_eq).symm
  rw [h_tsum1, h_tsum2,
    ← h_sum1.tsum_sub (h_sum_σ.mul_left (Real.Gamma a)⁻¹).summable]
  have h_sum_norm : Summable (fun n => ‖term1 n - term2 n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => by rw [Real.norm_eq_abs]; exact h_pt n) h_sum_dom.summable
  have h_norm_tsum := norm_tsum_le_tsum_norm h_sum_norm
  rw [Real.norm_eq_abs] at h_norm_tsum
  calc
    |∑' n : ℕ, (term1 n - term2 n)|
      ≤ ∑' n : ℕ, ‖term1 n - term2 n‖ := h_norm_tsum
    _ ≤ ∑' n : ℕ, dom n :=
        h_sum_norm.tsum_le_tsum
          (fun n => by rw [Real.norm_eq_abs]; exact h_pt n) h_sum_dom.summable
    _ = C_tot / (K : ℝ) := h_sum_dom.tsum_eq

/-!
## 3. Full and Outer `θ`-Integrals of the `t`-Channel Identity Projection
-/

/-- The full `[-π, π]` `θ`-integral of the `t`-channel identity contribution `crossIdentity Δ_phi`:
`∫_{-π}^{π} (dθ / π) e^{-J (w_r + iθ)} G_id(w_l - iθ, w_r + iθ)`. -/
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

/-- Fourier coefficient extraction from `crossFactor Δ_phi (wr + i θ)` on `[-π, π]`:
for `Δ_phi > 0`, `M ∈ ℕ`, and `wr ∈ UcDisk`,
`∫_{-π}^{π} e^{-i(Δ_φ + M)θ} crossFactor(Δ_φ, wr + iθ) dθ =`
`2π * 4^(Δ_φ) ((2Δ_φ)_M / M!) e^((Δ_φ + M) wr)`. -/
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
  have h_sum_real :=
    (hasSum_exp_mul_one_sub_exp_rpow_neg Δ_phi hwr).mul_left ((4 : ℝ) ^ Δ_phi)
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
        Real.norm_of_nonneg
          (mul_nonneg (by positivity) (pochhammerCoeff_nonneg (by positivity) m)),
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

/-- Exact binomial series evaluation of `identityProjSpinFull` on `[-π, π]` for `K ∈ ℕ` and
`wl, wr ∈ UcDisk`:
`identityProjSpinFull(Δ_φ, K, wl, wr) =`
`2 * 4^(2Δ_φ) e^(Δ_φ(wl + wr)) ∑_{n=0}^∞ ((2Δ_φ)_n / n!) ((2Δ_φ)_{n + K} / (n + K)!)`
`* e^(n(wl + wr))`. -/
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
        Real.norm_of_nonneg
          (mul_nonneg (by positivity) (pochhammerCoeff_nonneg (by positivity) n)),
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
              (Real.exp ((Δ_phi + (n : ℝ)) * wl.re) *
                Real.exp (- (K : ℝ) * wr.re)) * K_wr := by
            refine mul_le_mul_of_nonneg_left h_cf_le ?_
            exact mul_nonneg
              (mul_nonneg (by positivity) (pochhammerCoeff_nonneg (by positivity) n))
              (by positivity)
        _ = (4 : ℝ) ^ Δ_phi * Real.exp (- (K : ℝ) * wr.re) * K_wr *
              (pochhammerCoeff (2 * Δ_phi) n *
                Real.exp ((Δ_phi + (n : ℝ)) * wl.re)) := by ring
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

/-- On the negative real axis `σ < 0` with `σ + 1 / (2k) < 0`, the full `[-π, π]` `θ`-integral
`identityProjSpinFull` at `(σ + 1 / (2k), -1 / (2k))` equals
`(identityLaplaceReal Δ_phi (2k) σ : ℂ)`. -/
lemma identityProjSpinFull_eq_identityLaplaceReal {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) {k : ℕ}
    (hk : 1 ≤ k) {σ : ℝ} (hσl : σ + 1 / (2 * (k : ℝ)) < 0) :
    identityProjSpinFull Δ_phi (2 * (k : ℤ))
        (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ)) =
      (identityLaplaceReal Δ_phi (2 * k) σ : ℂ) := by
  have h2k_pos : (0 : ℝ) < 2 * (k : ℝ) := by exact_mod_cast (by omega : 0 < 2 * k)
  set wl : ℂ := ((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)
  set wr : ℂ := ((-1 / (2 * (k : ℝ)) : ℝ) : ℂ)
  have hwl : wl ∈ UcDisk := by rw [mem_UcDisk_iff]; simpa [wl] using hσl
  have hwr : wr ∈ UcDisk := by
    rw [mem_UcDisk_iff]
    exact div_neg_of_neg_of_pos (by norm_num) h2k_pos
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
      rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, add_mul,
        Real.exp_add, Real.exp_nat_mul]
    rw [hexp_cast]
    push_cast
    ring
  rw [← h_sum_real.tsum_eq, ← Complex.ofReal_tsum, tsum_mul_left]
  rfl

/-- **Uniform `O((2k)⁻¹)` Bound for `identityProjSpinFull` on `σ ≤ σ_plus < 0`**:
For `Δ_phi > 0` and `σ_plus < 0`, there exists `C ≥ 0` such that for all `k ≥ 1` and all
`σ ≤ σ_plus` with `σ + 1 / (2k) < 0`,
`‖(2k)^(1 - 2Δ_φ) identityProjSpinFull(Δ_φ, 2k, σ + 1/(2k), -1/(2k)) -`
`universalLaplaceReal(Δ_φ, σ)‖ ≤ C * (2k)^(-1)`. -/
theorem exists_uniform_bound_identityProjSpinFull_sub_universalLaplaceReal
    {Δ_phi σ_plus : ℝ} (hΔ : 0 < Δ_phi) (hσ_plus : σ_plus < 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {k : ℕ}, 1 ≤ k → ∀ {σ : ℝ}, σ ≤ σ_plus →
      σ + 1 / (2 * (k : ℝ)) < 0 →
      ‖(((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) : ℝ) : ℂ) *
          identityProjSpinFull Δ_phi (2 * (k : ℤ))
            (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ)) -
        (universalLaplaceReal Δ_phi σ : ℂ)‖ ≤
        C * (2 * (k : ℝ)) ^ (- (1 : ℝ)) := by
  have h2Δ : 0 < 2 * Δ_phi := by positivity
  obtain ⟨C₁, hC₁_nonneg, hC₁⟩ :=
    exists_uniform_bound_tsum_pochhammerCoeff_sub h2Δ hσ_plus
  refine ⟨2 * (4 : ℝ) ^ (2 * Δ_phi) * C₁, by positivity,
    fun {k} hk {σ} hσ hσl => ?_⟩
  have h2k_ge1 : 1 ≤ 2 * k := by omega
  have h2k_pos : (0 : ℝ) < 2 * (k : ℝ) := by exact_mod_cast (by omega : 0 < 2 * k)
  set wl : ℂ := ((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)
  set wr : ℂ := ((-1 / (2 * (k : ℝ)) : ℝ) : ℂ)
  have hwl : wl ∈ UcDisk := by rw [mem_UcDisk_iff]; simpa [wl] using hσl
  have hwr : wr ∈ UcDisk := by
    rw [mem_UcDisk_iff]
    exact div_neg_of_neg_of_pos (by norm_num) h2k_pos
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
      rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, add_mul,
        Real.exp_add, Real.exp_nat_mul]
    rw [hexp_cast]
    push_cast
    ring
  have h_id_eq :
      identityProjSpinFull Δ_phi (2 * (k : ℤ)) wl wr =
        (((2 * (4 : ℝ) ^ (2 * Δ_phi) * Real.exp (Δ_phi * σ)) *
          (∑' n : ℕ, pochhammerCoeff (2 * Δ_phi) n *
            pochhammerCoeff (2 * Δ_phi) (n + 2 * k) * (Real.exp σ) ^ n) : ℝ) : ℂ) := by
    rw [← h_sum_real.tsum_eq, ← Complex.ofReal_tsum, tsum_mul_left]
  rw [h_id_eq, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  have h_factor :
      (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) *
          (2 * (4 : ℝ) ^ (2 * Δ_phi) * Real.exp (Δ_phi * σ) *
            ∑' n : ℕ, pochhammerCoeff (2 * Δ_phi) n *
              pochhammerCoeff (2 * Δ_phi) (n + 2 * k) * (Real.exp σ) ^ n) -
        universalLaplaceReal Δ_phi σ =
      (2 * (4 : ℝ) ^ (2 * Δ_phi) * Real.exp (Δ_phi * σ)) *
        (((2 * k : ℕ) : ℝ) ^ (1 - 2 * Δ_phi) *
            (∑' n : ℕ, pochhammerCoeff (2 * Δ_phi) n *
              pochhammerCoeff (2 * Δ_phi) (n + 2 * k) * (Real.exp σ) ^ n) -
          (Real.Gamma (2 * Δ_phi))⁻¹ * (1 - Real.exp σ) ^ (- (2 * Δ_phi))) := by
    dsimp [universalLaplaceReal]
    push_cast
    ring
  rw [h_factor, abs_mul, abs_of_pos (by positivity)]
  have hexp_le1 : Real.exp (Δ_phi * σ) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hΔ.le (hσ.trans hσ_plus.le))
  have h_tsum_bd := hC₁ h2k_ge1 hσ
  have h_cast_r : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; rfl
  rw [h_cast_r] at h_tsum_bd
  have h_rpow_inv : C₁ / (2 * (k : ℝ)) = C₁ * (2 * (k : ℝ)) ^ (- (1 : ℝ)) := by
    rw [Real.rpow_neg h2k_pos.le, Real.rpow_one, div_eq_mul_inv]
  calc
    2 * (4 : ℝ) ^ (2 * Δ_phi) * Real.exp (Δ_phi * σ) *
        |((2 * k : ℕ) : ℝ) ^ (1 - 2 * Δ_phi) *
            (∑' n : ℕ, pochhammerCoeff (2 * Δ_phi) n *
              pochhammerCoeff (2 * Δ_phi) (n + 2 * k) * (Real.exp σ) ^ n) -
          (Real.Gamma (2 * Δ_phi))⁻¹ * (1 - Real.exp σ) ^ (- (2 * Δ_phi))|
      ≤ (2 * (4 : ℝ) ^ (2 * Δ_phi) * 1) * (C₁ / (2 * (k : ℝ))) := by
        rw [h_cast_r]
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hexp_le1 (by positivity))
          h_tsum_bd (abs_nonneg _) (by positivity)
    _ = 2 * (4 : ℝ) ^ (2 * Δ_phi) * C₁ * (2 * (k : ℝ)) ^ (- (1 : ℝ)) := by
        rw [h_rpow_inv]; ring

/-!
### Outer `θ`-Integral Bound on `[-π, -π/2] ∪ [π/2, π]`
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
    have hre :
        (Complex.log (1 - Complex.exp ((u : ℂ) + ((s * θ : ℝ) : ℂ) * I)) * (α : ℂ)).re =
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
  have h1 :
      HasDerivAt (fun x : ℝ => (u : ℂ) + ((s * x : ℝ) : ℂ) * I) ((s : ℂ) * I) θ := by
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

/-- One-step integration by parts bound for `∫_a^b e^{-i K θ} g(θ) dθ`:
if `a ≤ b`, `K > 0`, `g` has continuous derivative `g'` on `ℝ`, and
`‖g(θ)‖ ≤ M0, ‖g'(θ)‖ ≤ M1` on `[a, b]`, then
`‖∫_a^b e^{-i K θ} g(θ) dθ‖ ≤ (2 M0 + M1 (b - a)) / K`. -/
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
        = (-(I * I) * ((K : ℂ) / (K : ℂ))) *
            Complex.exp (- (K : ℂ) * (θ : ℂ) * I) := by ring
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

/-- Bound on `∫_a^b e^{-i K θ} (1 - e^(σ_l - iθ))^(-2Δ_φ) (1 - e^(σ_r + iθ))^(-2Δ_φ) dθ`
on any interval `[a, b]` where `cos θ ≤ 0`: for `Δ_phi > 0`, `σl < 0, σr < 0`, and `K > 0`,
`‖∫_a^b ... dθ‖ ≤ (2 + 4Δ_φ (b - a)) / K`. -/
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
            ‖(1 - Complex.exp ((σl : ℂ) + ((-1 * θ : ℝ) : ℂ) * I)) ^
              (((α - 1 : ℝ) : ℂ))‖ *
            Real.exp σl := by
        have h_abs_α : |α| = 2 * Δ_phi := by
          dsimp [α]; rw [abs_of_neg (by linarith)]; ring
        simp [gl', h_abs_α, Complex.norm_exp]
      have hexp_le : Real.exp σl ≤ 1 := Real.exp_le_one_iff.mpr hσl.le
      have hcpow_le :
          ‖(1 - Complex.exp ((σl : ℂ) + ((-1 * θ : ℝ) : ℂ) * I)) ^
            (((α - 1 : ℝ) : ℂ))‖ ≤ 1 :=
        norm_one_sub_exp_cpow_le_one_of_cos_nonpos hcos_l (by dsimp [α]; linarith)
      rw [h_norm_gl']
      calc
        2 * Δ_phi *
            ‖(1 - Complex.exp ((σl : ℂ) + ((-1 * θ : ℝ) : ℂ) * I)) ^
              (((α - 1 : ℝ) : ℂ))‖ *
            Real.exp σl
          ≤ (2 * Δ_phi * 1) * 1 :=
            mul_le_mul
              (mul_le_mul_of_nonneg_left hcpow_le (by positivity))
              hexp_le (Real.exp_pos σl).le (by positivity)
        _ = 2 * Δ_phi := by ring
    have hgr'_le : ‖gr' θ‖ ≤ 2 * Δ_phi := by
      have h_norm_gr' :
          ‖gr' θ‖ = (2 * Δ_phi) *
            ‖(1 - Complex.exp ((σr : ℂ) + ((1 * θ : ℝ) : ℂ) * I)) ^
              (((α - 1 : ℝ) : ℂ))‖ *
            Real.exp σr := by
        have h_abs_α : |α| = 2 * Δ_phi := by
          dsimp [α]; rw [abs_of_neg (by linarith)]; ring
        simp [gr', h_abs_α, Complex.norm_exp]
      have hexp_le : Real.exp σr ≤ 1 := Real.exp_le_one_iff.mpr hσr.le
      have hcpow_le :
          ‖(1 - Complex.exp ((σr : ℂ) + ((1 * θ : ℝ) : ℂ) * I)) ^
            (((α - 1 : ℝ) : ℂ))‖ ≤ 1 :=
        norm_one_sub_exp_cpow_le_one_of_cos_nonpos hcos_r (by dsimp [α]; linarith)
      rw [h_norm_gr']
      calc
        2 * Δ_phi *
            ‖(1 - Complex.exp ((σr : ℂ) + ((1 * θ : ℝ) : ℂ) * I)) ^
              (((α - 1 : ℝ) : ℂ))‖ *
            Real.exp σr
          ≤ (2 * Δ_phi * 1) * 1 :=
            mul_le_mul
              (mul_le_mul_of_nonneg_left hcpow_le (by positivity))
              hexp_le (Real.exp_pos σr).le (by positivity)
        _ = 2 * Δ_phi := by ring
    calc
      ‖gl' θ * gr θ + gl θ * gr' θ‖
        ≤ ‖gl' θ * gr θ‖ + ‖gl θ * gr' θ‖ := norm_add_le _ _
      _ = ‖gl' θ‖ * ‖gr θ‖ + ‖gl θ‖ * ‖gr' θ‖ := by
          rw [norm_mul (gl' θ), norm_mul (gl θ)]
      _ ≤ (2 * Δ_phi) * 1 + 1 * (2 * Δ_phi) :=
        add_le_add
          (mul_le_mul hgl'_le hgr_le (norm_nonneg _) (by positivity))
          (mul_le_mul hgl_le hgr'_le (norm_nonneg _) zero_le_one)
      _ = 4 * Δ_phi := by ring

/-- Factorization of `crossIdentity Δ_phi (wl - i θ) (wr + i θ)` separating the `θ`-independent
prefactor `4^(2Δ_φ) e^(Δ_φ (w_l + w_r))` from the `2π`-periodic factors. -/
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

/-- **Uniform `O((2k)^(-2Δ_φ))` Outer `θ`-Integral Bound**:
For `Δ_phi > 0`, there exists `C ≥ 0` such that for all `k ≥ 1` and all `σ < 0` with
`σ + 1 / (2k) < 0`, the rescaled outer integral `identityProjSpinFull - identityProjSpin` on
`[-π, -π/2] ∪ [π/2, π]` is bounded by `C * (2k)^(-2Δ_φ)`. -/
theorem exists_uniform_bound_identityProjSpinFull_sub_identityProjSpin_real
    {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {k : ℕ}, 1 ≤ k → ∀ {σ : ℝ}, σ < 0 →
      σ + 1 / (2 * (k : ℝ)) < 0 →
      ‖(((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) : ℝ) : ℂ) *
          (identityProjSpinFull Δ_phi (2 * (k : ℤ))
              (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ)) -
            identityProjSpin Δ_phi (2 * (k : ℤ))
              (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ)))‖ ≤
        C * (2 * (k : ℝ)) ^ (-2 * Δ_phi) := by
  set C_out : ℝ :=
    π⁻¹ * ((4 : ℝ) ^ (2 * Δ_phi) * Real.exp 1) * (2 * (2 + (4 * Δ_phi) * (π / 2)))
  refine ⟨C_out, by positivity, fun {k} hk1 {σ} hσ hσl => ?_⟩
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
  set c_k : ℂ := (((4 : ℝ) ^ (2 * Δ_phi) * Real.exp (Δ_phi * σ + 1) : ℝ) : ℂ)
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
  have hexp_le : Real.exp (Δ_phi * σ + 1) ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr (by nlinarith)
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
          (π⁻¹ * ((4 : ℝ) ^ (2 * Δ_phi) * Real.exp 1 *
            ((2 * (2 + (4 * Δ_phi) * (π / 2))) / K))) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul
              (mul_le_mul_of_nonneg_left hexp_le (by positivity))
              h_sum_b (norm_nonneg _) (by positivity))
            (by positivity))
          (by positivity)
    _ = C_out * (K ^ (1 - 2 * Δ_phi) / K) := by dsimp [C_out]; ring
    _ = C_out * K ^ (-2 * Δ_phi) := by rw [h_rpow]

/-!
## 4. Uniform Real-Axis Laplace Bounds on `[σ_minus, σ_plus] ⊂ (-∞, 0)`
-/

namespace MonomialFourPointData

variable (M : MonomialFourPointData)

/-- **Uniform `L¹` Modulus Bound on the Folded `θ`-Contour `[-π/2, π/2]`**:
For any compact negative interval `[σ_minus, σ_plus] ⊂ (-∞, 0)` and non-resonant twist gap
`2(h_gap - Δ_phi) ≠ -1`, the rescaled remainder on `[σ_minus, σ_plus]` is bounded uniformly by
`C * ((2k)^(-2 h_gap) + (2k)^(1 - 2Δ_φ))` whenever `σ_plus + 1 / (2k) ≤ σ_plus / 2`. -/
theorem exists_uniform_bound_fourierProjSpin_sub_identity_real {ν Δ_phi h_gap : ℝ}
    (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi)
    (hM : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      M.eval wl wr = corr.correlator_pdisk wl wr)
    (hgap : M.HasTwistGap h_gap) (h_ne : 2 * (h_gap - Δ_phi) ≠ -1)
    {σ_minus σ_plus : ℝ} (hσ_le : σ_minus ≤ σ_plus) (hσ_plus : σ_plus < 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {k : ℕ}, 1 ≤ k →
      σ_plus + 1 / (2 * (k : ℝ)) ≤ σ_plus / 2 →
      ∀ {σ : ℝ}, σ ∈ Icc σ_minus σ_plus →
      ‖(((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) : ℝ) : ℂ) *
          (M.fourierProjSpin (2 * (k : ℤ))
              (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ)) -
            identityProjSpin Δ_phi (2 * (k : ℤ))
              (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ)))‖ ≤
        C * ((2 * (k : ℝ)) ^ (-2 * h_gap) + (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi)) := by
  have hh_gap : 0 < h_gap := by
    rcases hgap with ⟨_, hlow, _, _⟩
    exact hlow.h_gap_pos
  have hσ_minus_neg : σ_minus < 0 := lt_of_le_of_lt hσ_le hσ_plus
  set σl0 := Real.log (1 - Real.sqrt 2 / 4 * Real.exp (σ_minus / 2))
  set σr0 := Real.log (1 - Real.sqrt 2 / 4 * Real.exp (-1 / 2))
  have hsqrt2_lt : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hσl0_neg : σl0 < 0 := by
    dsimp [σl0]
    have h_prod_pos : 0 < Real.sqrt 2 / 4 * Real.exp (σ_minus / 2) := by positivity
    have h_pos : 0 < 1 - Real.sqrt 2 / 4 * Real.exp (σ_minus / 2) := by
      have : Real.exp (σ_minus / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2),
        Real.exp_pos (σ_minus / 2)]
    exact Real.log_neg h_pos (by linarith)
  have hσr0_neg : σr0 < 0 := by
    dsimp [σr0]
    have h_prod_pos : 0 < Real.sqrt 2 / 4 * Real.exp (-1 / 2) := by positivity
    have h_pos : 0 < 1 - Real.sqrt 2 / 4 * Real.exp (-1 / 2) := by
      have : Real.exp (-1 / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2), Real.exp_pos (-1 / 2)]
    exact Real.log_neg h_pos (by linarith)
  rcases integral_norm_one_sub_exp_rpow_le h_ne with ⟨C_int, hC_int_nonneg, hC_int⟩
  set K_left := (4 : ℝ) ^ Δ_phi * (1 - Real.exp (σ_plus / 2)) ^ (-2 * Δ_phi)
  have h1_exp_σ2 : 0 < 1 - Real.exp (σ_plus / 2) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hK_left_nonneg : 0 ≤ K_left := by positivity
  set K_rem :=
    Real.exp (1 - h_gap * σr0) * K_left * (4 : ℝ) ^ Δ_phi * (M.evalReal σl0 σr0 - 1)
  have hK_rem_nonneg : 0 ≤ K_rem :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le hK_left_nonneg) (by positivity))
      (M.evalReal_sub_one_nonneg hgap σl0 σr0)
  refine ⟨π⁻¹ * K_rem * C_int, by positivity, fun {k} hk1 hσk {σ} hσ => ?_⟩
  have h2k_pos : (0 : ℝ) < 2 * (k : ℝ) := by exact_mod_cast (by omega : 0 < 2 * k)
  set ε := 1 / (2 * (k : ℝ))
  have hε_pos : 0 < ε := by positivity
  have hε_le : ε ≤ 1 / 2 := by
    dsimp [ε]
    have : (2 : ℝ) ≤ 2 * (k : ℝ) := by
      have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      linarith
    exact one_div_le_one_div_of_le (by norm_num) this
  set wl0 : ℂ := ((σ + ε : ℝ) : ℂ)
  set wr0 : ℂ := ((-ε : ℝ) : ℂ)
  have hwl0 : wl0 ∈ UcDisk := by
    rw [mem_UcDisk_iff]; dsimp [wl0]; linarith [hσ.2, hσk]
  have hwr0 : wr0 ∈ UcDisk := by
    rw [mem_UcDisk_iff]; dsimp [wr0]; simp [hε_pos]
  have h_sub_proj :
      M.fourierProjSpin (2 * (k : ℤ)) wl0 wr0 -
          identityProjSpin Δ_phi (2 * (k : ℤ)) wl0 wr0 =
        (π : ℂ)⁻¹ * ∫ θ in (-π / 2)..(π / 2),
          Complex.exp (- ((2 * (k : ℤ) : ℤ) : ℂ) * (wr0 + (θ : ℂ) * I)) *
            (M.eval (wl0 - (θ : ℂ) * I) (wr0 + (θ : ℂ) * I) -
              crossIdentity Δ_phi (wl0 - (θ : ℂ) * I) (wr0 + (θ : ℂ) * I)) := by
    dsimp [fourierProjSpin, identityProjSpin, fourierIntegrand]
    rw [← mul_sub, ← intervalIntegral.integral_sub]
    · congr 1
      refine intervalIntegral.integral_congr (fun θ _ => by ring)
    · exact (M.continuous_fourierIntegrand (2 * (k : ℤ)) hwl0 hwr0).intervalIntegrable _ _
    · have h1 : Continuous (fun θ : ℝ =>
          Complex.exp (- ((2 * (k : ℤ) : ℤ) : ℂ) * (wr0 + (θ : ℂ) * I))) := by fun_prop
      exact
        (h1.mul (continuous_crossIdentity_shift Δ_phi hwl0 hwr0)).intervalIntegrable _ _
  have h_wr0_eq : ((-1 / (2 * (k : ℝ)) : ℝ) : ℂ) = wr0 := by
    dsimp [wr0, ε]; ring_nf
  rw [h_wr0_eq, h_sub_proj, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (rpow_nonneg h2k_pos.le _)]
  have h_norm_pi : ‖(π : ℂ)⁻¹‖ = π⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [h_norm_pi]
  have h_cont_bound :
      Continuous (fun θ : ℝ =>
        K_rem *
          ‖1 - Complex.exp ((-ε : ℂ) + (θ : ℂ) * I)‖ ^ (2 * (h_gap - Δ_phi))) := by
    refine continuous_const.mul (Continuous.rpow_const (by fun_prop) (fun θ => Or.inl ?_))
    have hw : (-ε : ℂ) + (θ : ℂ) * I ∈ UcDisk := by
      rw [mem_UcDisk_iff]; simp [hε_pos]
    exact norm_ne_zero_iff.mpr (slitPlane_ne_zero (one_sub_exp_mem_slitPlane hw))
  have h_int_bound :
      ‖∫ θ in (-π / 2)..(π / 2),
          Complex.exp (- ((2 * (k : ℤ) : ℤ) : ℂ) * (wr0 + (θ : ℂ) * I)) *
            (M.eval (wl0 - (θ : ℂ) * I) (wr0 + (θ : ℂ) * I) -
              crossIdentity Δ_phi (wl0 - (θ : ℂ) * I) (wr0 + (θ : ℂ) * I))‖ ≤
        ∫ θ in (-π / 2)..(π / 2),
          K_rem *
            ‖1 - Complex.exp ((-ε : ℂ) + (θ : ℂ) * I)‖ ^ (2 * (h_gap - Δ_phi)) := by
    refine intervalIntegral.norm_integral_le_of_norm_le (by linarith [Real.pi_pos])
      (Eventually.of_forall (fun θ hθ => ?_)) (h_cont_bound.intervalIntegrable _ _)
    have hθ_Icc : θ ∈ Icc (-π / 2) (π / 2) := ⟨hθ.1.le, hθ.2⟩
    have h_neg_θ_Icc : -θ ∈ Icc (-π / 2) (π / 2) :=
      ⟨by linarith [hθ.2], by linarith [hθ.1.le]⟩
    set wl := wl0 - (θ : ℂ) * I
    set wr := wr0 + (θ : ℂ) * I
    have hwl : wl ∈ UcDisk := sub_I_mul_mem_UcDisk hwl0 θ
    have hwr : wr ∈ UcDisk := add_I_mul_mem_UcDisk hwr0 θ
    have hwl_im : wl.im ∈ Ioo (-π) π := by
      dsimp [wl, wl0]
      simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero,
        zero_sub, mem_Ioo, neg_lt_neg_iff]
      exact ⟨by linarith [hθ.2, Real.pi_pos], by linarith [hθ.1.le, Real.pi_pos]⟩
    have hwr_im : wr.im ∈ Ioo (-π) π := by
      dsimp [wr, wr0]
      simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero,
        zero_add, mem_Ioo]
      exact ⟨by linarith [hθ.1.le, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
    have hwl_cross : (crossW wl).re ≤ σl0 := by
      refine re_crossW_le_of_re_ge hwl ?_ ?_
      · dsimp [wl, wl0]; simp; linarith [hσ.1, hε_pos]
      · dsimp [wl, wl0]; simpa using h_neg_θ_Icc
    have hwr_cross : (crossW wr).re ≤ σr0 := by
      refine re_crossW_le_of_re_ge hwr ?_ ?_
      · dsimp [wr, wr0]; simp; linarith
      · dsimp [wr, wr0]; simpa using hθ_Icc
    have h_exp_norm : ‖Complex.exp (- ((2 * (k : ℤ) : ℤ) : ℂ) * wr)‖ = Real.exp 1 := by
      rw [Complex.norm_exp]
      congr 1
      dsimp [wr, wr0, ε]
      have hre : (- ((2 * (k : ℤ) : ℤ) : ℂ) *
          (((-(1 / (2 * (k : ℝ))) : ℝ) : ℂ) + (θ : ℂ) * I)).re =
          (2 * (k : ℝ)) * (1 / (2 * (k : ℝ))) := by
        simp [Complex.mul_re]
      rw [hre, mul_one_div_cancel h2k_pos.ne']
    rw [norm_mul, h_exp_norm]
    have h_pt := M.norm_eval_sub_crossIdentity_le_of_re_le corr hν hM hgap
      hσl0_neg hσr0_neg hwl hwr hwl_im hwr_im hwl_cross hwr_cross
    have h_cf_l : ‖crossFactor Δ_phi wl‖ ≤ K_left := by
      refine norm_crossFactor_le_of_re_le hΔ (by linarith) hwl ?_
      dsimp [wl, wl0]; simp; linarith [hσ.2, hσk]
    have h_cf_r : ‖crossFactor Δ_phi wr‖ * Real.exp (h_gap * (crossW wr).re) ≤
        (4 : ℝ) ^ Δ_phi *
          ‖1 - Complex.exp ((-ε : ℂ) + (θ : ℂ) * I)‖ ^ (2 * (h_gap - Δ_phi)) := by
      have hwr_eq : wr = (-ε : ℂ) + (θ : ℂ) * I := by dsimp [wr, wr0]; push_cast; rfl
      rw [← hwr_eq]
      exact norm_crossFactor_mul_exp_re_crossW_le hΔ hh_gap hwr
        (by dsimp [wr, wr0]; simpa using hθ_Icc)
    have h_ci : ‖crossIdentity Δ_phi wl wr‖ *
        (Real.exp (h_gap * ((crossW wr).re - σr0)) * (M.evalReal σl0 σr0 - 1)) =
        (‖crossFactor Δ_phi wl‖ *
          (‖crossFactor Δ_phi wr‖ * Real.exp (h_gap * (crossW wr).re))) *
          (Real.exp (- (h_gap * σr0)) * (M.evalReal σl0 σr0 - 1)) := by
      dsimp [crossIdentity]
      rw [norm_mul, mul_sub h_gap, Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg]
      ring
    rw [h_ci] at h_pt
    have h_prod_le :
        ‖crossFactor Δ_phi wl‖ *
          (‖crossFactor Δ_phi wr‖ * Real.exp (h_gap * (crossW wr).re)) ≤
          K_left * ((4 : ℝ) ^ Δ_phi *
            ‖1 - Complex.exp ((-ε : ℂ) + (θ : ℂ) * I)‖ ^ (2 * (h_gap - Δ_phi))) :=
      mul_le_mul h_cf_l h_cf_r (by positivity) hK_left_nonneg
    calc
      Real.exp 1 * ‖M.eval wl wr - crossIdentity Δ_phi wl wr‖
        ≤ Real.exp 1 * ((K_left * ((4 : ℝ) ^ Δ_phi *
            ‖1 - Complex.exp ((-ε : ℂ) + (θ : ℂ) * I)‖ ^ (2 * (h_gap - Δ_phi)))) *
            (Real.exp (- (h_gap * σr0)) * (M.evalReal σl0 σr0 - 1))) := by
          refine mul_le_mul_of_nonneg_left (h_pt.trans ?_) (Real.exp_pos 1).le
          exact mul_le_mul_of_nonneg_right h_prod_le
            (mul_nonneg (Real.exp_pos _).le (M.evalReal_sub_one_nonneg hgap σl0 σr0))
      _ = K_rem *
            ‖1 - Complex.exp ((-ε : ℂ) + (θ : ℂ) * I)‖ ^ (2 * (h_gap - Δ_phi)) := by
        dsimp [K_rem]
        rw [Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg]
        ring
  rw [intervalIntegral.integral_const_mul] at h_int_bound
  have h_rpow_alg :
      (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * (ε ^ (2 * (h_gap - Δ_phi) + 1) + 1) =
        (2 * (k : ℝ)) ^ (-2 * h_gap) + (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) := by
    rw [mul_add, mul_one]
    congr 1
    dsimp [ε]
    rw [one_div, Real.inv_rpow h2k_pos.le, ← Real.rpow_neg h2k_pos.le,
      ← Real.rpow_add h2k_pos]
    ring_nf
  calc
    (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) *
        (π⁻¹ * ‖∫ θ in (-π / 2)..(π / 2),
          Complex.exp (- ((2 * (k : ℤ) : ℤ) : ℂ) * (wr0 + (θ : ℂ) * I)) *
            (M.eval (wl0 - (θ : ℂ) * I) (wr0 + (θ : ℂ) * I) -
              crossIdentity Δ_phi (wl0 - (θ : ℂ) * I) (wr0 + (θ : ℂ) * I))‖)
      ≤ (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) *
          (π⁻¹ * (K_rem * (C_int * (ε ^ (2 * (h_gap - Δ_phi) + 1) + 1)))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity))
          (by positivity)
        exact h_int_bound.trans
          (mul_le_mul_of_nonneg_left (hC_int hε_pos hε_le) hK_rem_nonneg)
    _ = (π⁻¹ * K_rem * C_int) *
          ((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) *
            (ε ^ (2 * (h_gap - Δ_phi) + 1) + 1)) := by ring
    _ = (π⁻¹ * K_rem * C_int) *
          ((2 * (k : ℝ)) ^ (-2 * h_gap) + (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi)) := by
      rw [h_rpow_alg]

/-- **Uniform Real-Axis Laplace Upper and Error Bounds on `[σ_minus, σ_plus] ⊂ (-∞, 0)`**:
For `Δ_phi > 1/2`, a twist gap `h_gap > 0` with `2(h_gap - Δ_phi) ≠ -1`, and any compact negative
interval `[σ_minus, σ_plus] ⊂ (-∞, 0)`, setting
`α := min (2 * h_gap) (min 1 (2 * Δ_phi - 1)) > 0`, there exist constants `M_bd > 0` and
`C_bd > 0` such that for all `k ≥ 1` and all `σ ∈ [σ_minus, σ_plus]`:
1. `(2k)^(1 - 2Δ_φ) L_{2k}(σ) + universalLaplaceReal(Δ_φ, σ) ≤ M_bd`,
2. `|(2k)^(1 - 2Δ_φ) L_{2k}(σ) - universalLaplaceReal(Δ_φ, σ)| ≤ C_bd * (2k)^(-α)`. -/
theorem exists_uniform_laplaceSpinReal_bounds {ν Δ_phi h_gap : ℝ}
    (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν) (hΔ : 1 / 2 < Δ_phi)
    (hM : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      M.eval wl wr = corr.correlator_pdisk wl wr)
    (hgap : M.HasTwistGap h_gap) (h_ne : 2 * (h_gap - Δ_phi) ≠ -1)
    {σ_minus σ_plus : ℝ} (hσ_le : σ_minus ≤ σ_plus) (hσ_plus : σ_plus < 0) :
    let α := min (2 * h_gap) (min 1 (2 * Δ_phi - 1))
    0 < α ∧ ∃ M_bd > 0, ∃ C_bd > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {σ : ℝ}, σ ∈ Icc σ_minus σ_plus →
        (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ +
          universalLaplaceReal Δ_phi σ ≤ M_bd ∧
        |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ -
          universalLaplaceReal Δ_phi σ| ≤ C_bd * (2 * (k : ℝ)) ^ (-α) := by
  intro α
  have hΔ_pos : 0 < Δ_phi := by linarith
  have hh_gap : 0 < h_gap := by
    rcases hgap with ⟨_, hlow, _, _⟩
    exact hlow.h_gap_pos
  have hα_pos : 0 < α := by
    dsimp [α]
    refine lt_min (by positivity) (lt_min zero_lt_one (by linarith))
  refine ⟨hα_pos, ?_⟩
  obtain ⟨C_rem, hC_rem_nonneg, hC_rem⟩ :=
    M.exists_uniform_bound_fourierProjSpin_sub_identity_real
      corr hν hΔ_pos hM hgap h_ne hσ_le hσ_plus
  obtain ⟨C_full, hC_full_nonneg, hC_full⟩ :=
    exists_uniform_bound_identityProjSpinFull_sub_universalLaplaceReal hΔ_pos hσ_plus
  obtain ⟨C_out, hC_out_nonneg, hC_out⟩ :=
    exists_uniform_bound_identityProjSpinFull_sub_identityProjSpin_real hΔ_pos
  set k₀ : ℕ := ⌈1 / (-σ_plus)⌉₊ + 1
  set C_large : ℝ := 2 * C_rem + C_full + C_out + 1
  have hC_large_pos : 0 < C_large := by dsimp [C_large]; positivity
  have h_large : ∀ {k : ℕ}, k₀ ≤ k → ∀ {σ : ℝ}, σ ∈ Icc σ_minus σ_plus →
      |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ -
        universalLaplaceReal Δ_phi σ| ≤ C_large * (2 * (k : ℝ)) ^ (-α) := by
    intro k hk σ hσ
    have hk1 : 1 ≤ k := by dsimp [k₀] at hk; omega
    have h2k_ge1 : (1 : ℝ) ≤ 2 * (k : ℝ) := by
      have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      linarith
    have h2k_pos : (0 : ℝ) < 2 * (k : ℝ) := by linarith
    have h_neg_pos : 0 < -σ_plus := neg_pos.mpr hσ_plus
    have hk_ge_inv : 1 / (-σ_plus) ≤ (k : ℝ) := by
      have h1 : 1 / (-σ_plus) ≤ (⌈1 / (-σ_plus)⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : (⌈1 / (-σ_plus)⌉₊ : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast (by dsimp [k₀] at hk; omega : ⌈1 / (-σ_plus)⌉₊ ≤ k)
      exact h1.trans h2
    have hσk : σ_plus + 1 / (2 * (k : ℝ)) ≤ σ_plus / 2 := by
      have h1 : 1 ≤ (k : ℝ) * (-σ_plus) := (div_le_iff₀ h_neg_pos).mp hk_ge_inv
      have h2 : 1 / (2 * (k : ℝ)) ≤ -σ_plus / 2 := by
        rw [div_le_div_iff₀ h2k_pos (by norm_num)]
        linarith
      linarith
    have hσl : σ + 1 / (2 * (k : ℝ)) < 0 := by linarith [hσ.2, hσk]
    have hσr : -1 / (2 * (k : ℝ)) < 0 := div_neg_of_neg_of_pos (by norm_num) h2k_pos
    have h_even : Even (2 * (k : ℤ)) := even_two_mul (k : ℤ)
    have h_eq := M.laplaceSpinReal_eq_fourierProjSpin h_even hσl hσr
    have h_add : (σ + 1 / (2 * (k : ℝ))) + (-1 / (2 * (k : ℝ))) = σ := by ring
    rw [h_add] at h_eq
    have h_cast_diff :
        |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ -
          universalLaplaceReal Δ_phi σ| =
        ‖(((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) : ℝ) : ℂ) *
            M.fourierProjSpin (2 * (k : ℤ))
              (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ)) -
          (universalLaplaceReal Δ_phi σ : ℂ)‖ := by
      rw [← h_eq, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs]
    rw [h_cast_diff]
    have hb_rem := hC_rem hk1 hσk hσ
    have hb_full := hC_full hk1 hσ.2 hσl
    have hb_out := hC_out hk1 (lt_of_le_of_lt hσ.2 hσ_plus) hσl
    set F_spin := M.fourierProjSpin (2 * (k : ℤ))
      (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ))
    set I_spin := identityProjSpin Δ_phi (2 * (k : ℤ))
      (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ))
    set IF_spin := identityProjSpinFull Δ_phi (2 * (k : ℤ))
      (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ))
    set scale : ℂ := (((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) : ℝ) : ℂ)
    have h_split :
        scale * F_spin - (universalLaplaceReal Δ_phi σ : ℂ) =
          scale * (F_spin - I_spin) - scale * (IF_spin - I_spin) +
            (scale * IF_spin - (universalLaplaceReal Δ_phi σ : ℂ)) := by ring
    have h_tri :
        ‖scale * F_spin - (universalLaplaceReal Δ_phi σ : ℂ)‖ ≤
          ‖scale * (F_spin - I_spin)‖ + ‖scale * (IF_spin - I_spin)‖ +
            ‖scale * IF_spin - (universalLaplaceReal Δ_phi σ : ℂ)‖ := by
      rw [h_split]
      exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    have hr1 : (2 * (k : ℝ)) ^ (-2 * h_gap) ≤ (2 * (k : ℝ)) ^ (-α) := by
      refine Real.rpow_le_rpow_of_exponent_le h2k_ge1 ?_
      have : α ≤ 2 * h_gap := min_le_left _ _
      linarith
    have hr2 : (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) ≤ (2 * (k : ℝ)) ^ (-α) := by
      refine Real.rpow_le_rpow_of_exponent_le h2k_ge1 ?_
      have : α ≤ 2 * Δ_phi - 1 := (min_le_right _ _).trans (min_le_right _ _)
      linarith
    have hr3 : (2 * (k : ℝ)) ^ (- (1 : ℝ)) ≤ (2 * (k : ℝ)) ^ (-α) := by
      refine Real.rpow_le_rpow_of_exponent_le h2k_ge1 ?_
      have : α ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
      linarith
    have hr4 : (2 * (k : ℝ)) ^ (-2 * Δ_phi) ≤ (2 * (k : ℝ)) ^ (-α) := by
      refine Real.rpow_le_rpow_of_exponent_le h2k_ge1 ?_
      have : α ≤ 2 * Δ_phi - 1 := (min_le_right _ _).trans (min_le_right _ _)
      linarith
    have h_rpow_pos : 0 ≤ (2 * (k : ℝ)) ^ (-α) := by positivity
    calc
      ‖scale * F_spin - (universalLaplaceReal Δ_phi σ : ℂ)‖
        ≤ C_rem * ((2 * (k : ℝ)) ^ (-2 * h_gap) + (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi)) +
            C_out * (2 * (k : ℝ)) ^ (-2 * Δ_phi) +
            C_full * (2 * (k : ℝ)) ^ (- (1 : ℝ)) :=
          h_tri.trans (add_le_add (add_le_add hb_rem hb_out) hb_full)
      _ ≤ C_rem * ((2 * (k : ℝ)) ^ (-α) + (2 * (k : ℝ)) ^ (-α)) +
            C_out * (2 * (k : ℝ)) ^ (-α) +
            C_full * (2 * (k : ℝ)) ^ (-α) := by
          refine add_le_add
            (add_le_add
              (mul_le_mul_of_nonneg_left (add_le_add hr1 hr2) hC_rem_nonneg)
              (mul_le_mul_of_nonneg_left hr4 hC_out_nonneg))
            (mul_le_mul_of_nonneg_left hr3 hC_full_nonneg)
      _ ≤ C_large * (2 * (k : ℝ)) ^ (-α) := by
          dsimp [C_large]
          nlinarith
  set U_plus : ℝ :=
    (2 * (4 : ℝ) ^ (2 * Δ_phi) / Real.Gamma (2 * Δ_phi)) *
      (1 - Real.exp σ_plus) ^ (- (2 * Δ_phi))
  have h1_exp_plus : 0 < 1 - Real.exp σ_plus :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr hσ_plus)
  have hU_plus_pos : 0 < U_plus := by
    dsimp [U_plus]
    have := Real.Gamma_pos_of_pos (by positivity : 0 < 2 * Δ_phi)
    positivity
  have h_univ_le : ∀ {σ : ℝ}, σ ∈ Icc σ_minus σ_plus →
      universalLaplaceReal Δ_phi σ ≤ U_plus := by
    intro σ hσ
    dsimp [universalLaplaceReal, U_plus]
    have hexp_le1 : Real.exp (Δ_phi * σ) ≤ 1 :=
      Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonneg_of_nonpos hΔ_pos.le (hσ.2.trans hσ_plus.le))
    have h1_sub_ge : 1 - Real.exp σ_plus ≤ 1 - Real.exp σ :=
      sub_le_sub_left (Real.exp_le_exp.mpr hσ.2) 1
    have hrpow_le :
        (1 - Real.exp σ) ^ (- (2 * Δ_phi)) ≤ (1 - Real.exp σ_plus) ^ (- (2 * Δ_phi)) :=
      Real.rpow_le_rpow_of_nonpos h1_exp_plus h1_sub_ge (by linarith)
    have h_pref_nonneg : 0 ≤ 2 * (4 : ℝ) ^ (2 * Δ_phi) / Real.Gamma (2 * Δ_phi) := by
      have := Real.Gamma_pos_of_pos (by positivity : 0 < 2 * Δ_phi)
      positivity
    have h1_exp_σ : 0 < 1 - Real.exp σ :=
      sub_pos.mpr (Real.exp_lt_one_iff.mpr (lt_of_le_of_lt hσ.2 hσ_plus))
    calc
      2 * (4 : ℝ) ^ (2 * Δ_phi) / Real.Gamma (2 * Δ_phi) *
          Real.exp (Δ_phi * σ) * (1 - Real.exp σ) ^ (- (2 * Δ_phi))
        ≤ (2 * (4 : ℝ) ^ (2 * Δ_phi) / Real.Gamma (2 * Δ_phi) * 1) *
            (1 - Real.exp σ_plus) ^ (- (2 * Δ_phi)) :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left hexp_le1 h_pref_nonneg)
            hrpow_le (Real.rpow_pos_of_pos h1_exp_σ _).le
            (mul_nonneg h_pref_nonneg zero_le_one)
      _ = U_plus := by dsimp [U_plus]; ring
  set B_fin : ℝ :=
    ∑ j ∈ Finset.range (k₀ + 1),
      (2 * (j : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (j : ℤ)) σ_plus
  have hB_fin_nonneg : 0 ≤ B_fin :=
    Finset.sum_nonneg fun j _ =>
      mul_nonneg (by positivity) (M.laplaceSpinReal_nonneg _ _)
  set M_bd : ℝ := B_fin + 2 * U_plus + C_large
  have hM_bd_pos : 0 < M_bd := by dsimp [M_bd]; positivity
  set C_bd : ℝ := max C_large (M_bd * (2 * (k₀ : ℝ)) ^ α)
  have hC_bd_pos : 0 < C_bd := lt_of_lt_of_le hC_large_pos (le_max_left _ _)
  refine ⟨M_bd, hM_bd_pos, C_bd, hC_bd_pos, fun {k} hk1 {σ} hσ => ?_⟩
  have hσ_neg : σ < 0 := lt_of_le_of_lt hσ.2 hσ_plus
  have h_L_nonneg :
      0 ≤ (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ :=
    mul_nonneg (by positivity) (M.laplaceSpinReal_nonneg _ _)
  have h_U_nonneg : 0 ≤ universalLaplaceReal Δ_phi σ :=
    universalLaplaceReal_nonneg hΔ_pos hσ_neg
  have h_U_bd : universalLaplaceReal Δ_phi σ ≤ U_plus := h_univ_le hσ
  have h2k_ge1 : (1 : ℝ) ≤ 2 * (k : ℝ) := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    linarith
  have h2k_pos : (0 : ℝ) < 2 * (k : ℝ) := by linarith
  rcases le_or_gt k₀ k with hk_ge | hk_lt
  · have h_err := h_large hk_ge hσ
    have hrpow_le1 : (2 * (k : ℝ)) ^ (-α) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos h2k_ge1 (by linarith)
    have h_err_le_C :
        |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ -
          universalLaplaceReal Δ_phi σ| ≤ C_large :=
      h_err.trans (by nlinarith)
    have h_L_le :
        (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ ≤
          U_plus + C_large := by
      linarith [(abs_le.mp h_err_le_C).2]
    refine ⟨by dsimp [M_bd]; linarith, ?_⟩
    exact h_err.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have h_mono :=
      M.laplaceSpinReal_mono (2 * (k : ℤ)) hσ_neg hσ_plus hσ.2
    have h_L_le_B :
        (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ ≤ B_fin := by
      calc
        (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ
          ≤ (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) *
              M.laplaceSpinReal (2 * (k : ℤ)) σ_plus :=
            mul_le_mul_of_nonneg_left h_mono (by positivity)
        _ ≤ B_fin :=
            Finset.single_le_sum
              (f := fun j : ℕ =>
                (2 * (j : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (j : ℤ)) σ_plus)
              (fun j _ => mul_nonneg (by positivity) (M.laplaceSpinReal_nonneg _ _))
              (Finset.mem_range.mpr (Nat.lt_succ_of_le hk_lt.le))
    have h_sum_le :
        (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ +
          universalLaplaceReal Δ_phi σ ≤ M_bd := by
      dsimp [M_bd]; linarith
    refine ⟨h_sum_le, ?_⟩
    have h_abs_le_M :
        |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ -
          universalLaplaceReal Δ_phi σ| ≤ M_bd := by
      refine (abs_sub _ _).trans ?_
      rw [abs_of_nonneg h_L_nonneg, abs_of_nonneg h_U_nonneg]
      exact h_sum_le
    have h2k_le_2k₀ : 2 * (k : ℝ) ≤ 2 * (k₀ : ℝ) := by
      have : (k : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast hk_lt.le
      linarith
    have h_rpow_le : (2 * (k : ℝ)) ^ α ≤ (2 * (k₀ : ℝ)) ^ α :=
      Real.rpow_le_rpow h2k_pos.le h2k_le_2k₀ hα_pos.le
    have h_canc : (2 * (k : ℝ)) ^ α * (2 * (k : ℝ)) ^ (-α) = 1 := by
      rw [← Real.rpow_add h2k_pos, add_neg_cancel, Real.rpow_zero]
    have h_one_le : 1 ≤ (2 * (k₀ : ℝ)) ^ α * (2 * (k : ℝ)) ^ (-α) := by
      rw [← h_canc]
      exact mul_le_mul_of_nonneg_right h_rpow_le (by positivity)
    calc
      |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ -
          universalLaplaceReal Δ_phi σ|
        ≤ M_bd * 1 := by linarith
      _ ≤ M_bd * ((2 * (k₀ : ℝ)) ^ α * (2 * (k : ℝ)) ^ (-α)) :=
          mul_le_mul_of_nonneg_left h_one_le hM_bd_pos.le
      _ = (M_bd * (2 * (k₀ : ℝ)) ^ α) * (2 * (k : ℝ)) ^ (-α) := by ring
      _ ≤ C_bd * (2 * (k : ℝ)) ^ (-α) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- **Uniform Real-Axis Laplace Upper and Error Bounds Against the Exact `t`-Channel Identity**:
For `Δ_phi > 1/2`, a twist gap `h_gap > 0` with `2(h_gap - Δ_phi) ≠ -1`, and any compact negative
interval `[σ_minus, σ_plus] ⊂ (-∞, 0)`, retaining all `1 / (2k)^m` subleading `t`-channel identity
binomial coefficients in `identityLaplaceReal Δ_phi (2k) σ` eliminates the `O((2k)⁻¹)` asymptotic
Gamma approximation error, giving the sharper exponent
`α := min (2 * h_gap) (2 * Δ_phi - 1) > 0`:
there exist constants `M_bd > 0` and `C_bd > 0` such that for all `k ≥ 1` and all
`σ ∈ [σ_minus, σ_plus]`:
1. `(2k)^(1 - 2Δ_φ) (L_{2k}(σ) + identityLaplaceReal(Δ_φ, 2k, σ)) ≤ M_bd`,
2. `(2k)^(1 - 2Δ_φ) |L_{2k}(σ) - identityLaplaceReal(Δ_φ, 2k, σ)| ≤ C_bd * (2k)^(-α)`. -/
theorem exists_uniform_laplaceSpinReal_sub_identity_bounds {ν Δ_phi h_gap : ℝ}
    (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν) (hΔ : 1 / 2 < Δ_phi)
    (hM : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      M.eval wl wr = corr.correlator_pdisk wl wr)
    (hgap : M.HasTwistGap h_gap) (h_ne : 2 * (h_gap - Δ_phi) ≠ -1)
    {σ_minus σ_plus : ℝ} (hσ_le : σ_minus ≤ σ_plus) (hσ_plus : σ_plus < 0) :
    let α := min (2 * h_gap) (2 * Δ_phi - 1)
    0 < α ∧ ∃ M_bd > 0, ∃ C_bd > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {σ : ℝ}, σ ∈ Icc σ_minus σ_plus →
        (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ +
          (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityLaplaceReal Δ_phi (2 * k) σ ≤ M_bd ∧
        |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ -
          (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityLaplaceReal Δ_phi (2 * k) σ| ≤
          C_bd * (2 * (k : ℝ)) ^ (-α) := by
  intro α
  have hΔ_pos : 0 < Δ_phi := by linarith
  have hh_gap : 0 < h_gap := by
    rcases hgap with ⟨_, hlow, _, _⟩
    exact hlow.h_gap_pos
  have hα_pos : 0 < α := lt_min (by positivity) (by linarith)
  refine ⟨hα_pos, ?_⟩
  obtain ⟨C_rem, hC_rem_nonneg, hC_rem⟩ :=
    M.exists_uniform_bound_fourierProjSpin_sub_identity_real
      corr hν hΔ_pos hM hgap h_ne hσ_le hσ_plus
  obtain ⟨C_full, hC_full_nonneg, hC_full⟩ :=
    exists_uniform_bound_identityProjSpinFull_sub_universalLaplaceReal hΔ_pos hσ_plus
  obtain ⟨C_out, hC_out_nonneg, hC_out⟩ :=
    exists_uniform_bound_identityProjSpinFull_sub_identityProjSpin_real hΔ_pos
  set k₀ : ℕ := ⌈1 / (-σ_plus)⌉₊ + 1
  set C_large : ℝ := 2 * C_rem + C_out + 1
  have hC_large_pos : 0 < C_large := by dsimp [C_large]; positivity
  have h_large : ∀ {k : ℕ}, k₀ ≤ k → ∀ {σ : ℝ}, σ ∈ Icc σ_minus σ_plus →
      |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ -
        (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityLaplaceReal Δ_phi (2 * k) σ| ≤
        C_large * (2 * (k : ℝ)) ^ (-α) := by
    intro k hk σ hσ
    have hk1 : 1 ≤ k := by dsimp [k₀] at hk; omega
    have h2k_ge1 : (1 : ℝ) ≤ 2 * (k : ℝ) := by
      have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      linarith
    have h2k_pos : (0 : ℝ) < 2 * (k : ℝ) := by linarith
    have h_neg_pos : 0 < -σ_plus := neg_pos.mpr hσ_plus
    have hk_ge_inv : 1 / (-σ_plus) ≤ (k : ℝ) := by
      have h1 : 1 / (-σ_plus) ≤ (⌈1 / (-σ_plus)⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : (⌈1 / (-σ_plus)⌉₊ : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast (by dsimp [k₀] at hk; omega : ⌈1 / (-σ_plus)⌉₊ ≤ k)
      exact h1.trans h2
    have hσk : σ_plus + 1 / (2 * (k : ℝ)) ≤ σ_plus / 2 := by
      have h1 : 1 ≤ (k : ℝ) * (-σ_plus) := (div_le_iff₀ h_neg_pos).mp hk_ge_inv
      have h2 : 1 / (2 * (k : ℝ)) ≤ -σ_plus / 2 := by
        rw [div_le_div_iff₀ h2k_pos (by norm_num)]
        linarith
      linarith
    have hσl : σ + 1 / (2 * (k : ℝ)) < 0 := by linarith [hσ.2, hσk]
    have hσr : -1 / (2 * (k : ℝ)) < 0 := div_neg_of_neg_of_pos (by norm_num) h2k_pos
    have h_even : Even (2 * (k : ℤ)) := even_two_mul (k : ℤ)
    have h_eq := M.laplaceSpinReal_eq_fourierProjSpin h_even hσl hσr
    have h_add : (σ + 1 / (2 * (k : ℝ))) + (-1 / (2 * (k : ℝ))) = σ := by ring
    rw [h_add] at h_eq
    have h_id_eq := identityProjSpinFull_eq_identityLaplaceReal hΔ_pos hk1 hσl
    have h_cast_diff :
        |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ -
          (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityLaplaceReal Δ_phi (2 * k) σ| =
        ‖(((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) : ℝ) : ℂ) *
            M.fourierProjSpin (2 * (k : ℤ))
              (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ)) -
          (((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) : ℝ) : ℂ) *
            identityProjSpinFull Δ_phi (2 * (k : ℤ))
              (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ))‖ := by
      rw [← h_eq, h_id_eq, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs]
    rw [h_cast_diff]
    have hb_rem := hC_rem hk1 hσk hσ
    have hb_out := hC_out hk1 (lt_of_le_of_lt hσ.2 hσ_plus) hσl
    set F_spin := M.fourierProjSpin (2 * (k : ℤ))
      (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ))
    set I_spin := identityProjSpin Δ_phi (2 * (k : ℤ))
      (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ))
    set IF_spin := identityProjSpinFull Δ_phi (2 * (k : ℤ))
      (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ))
    set scale : ℂ := (((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) : ℝ) : ℂ)
    have h_split :
        scale * F_spin - scale * IF_spin =
          scale * (F_spin - I_spin) - scale * (IF_spin - I_spin) := by ring
    have h_tri :
        ‖scale * F_spin - scale * IF_spin‖ ≤
          ‖scale * (F_spin - I_spin)‖ + ‖scale * (IF_spin - I_spin)‖ := by
      rw [h_split]
      exact norm_sub_le _ _
    have hr1 : (2 * (k : ℝ)) ^ (-2 * h_gap) ≤ (2 * (k : ℝ)) ^ (-α) := by
      refine Real.rpow_le_rpow_of_exponent_le h2k_ge1 ?_
      have : α ≤ 2 * h_gap := min_le_left _ _
      linarith
    have hr2 : (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) ≤ (2 * (k : ℝ)) ^ (-α) := by
      refine Real.rpow_le_rpow_of_exponent_le h2k_ge1 ?_
      have : α ≤ 2 * Δ_phi - 1 := min_le_right _ _
      linarith
    have hr4 : (2 * (k : ℝ)) ^ (-2 * Δ_phi) ≤ (2 * (k : ℝ)) ^ (-α) := by
      refine Real.rpow_le_rpow_of_exponent_le h2k_ge1 ?_
      have : α ≤ 2 * Δ_phi - 1 := min_le_right _ _
      linarith
    have h_rpow_pos : 0 ≤ (2 * (k : ℝ)) ^ (-α) := by positivity
    calc
      ‖scale * F_spin - scale * IF_spin‖
        ≤ C_rem * ((2 * (k : ℝ)) ^ (-2 * h_gap) + (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi)) +
            C_out * (2 * (k : ℝ)) ^ (-2 * Δ_phi) :=
          h_tri.trans (add_le_add hb_rem hb_out)
      _ ≤ C_rem * ((2 * (k : ℝ)) ^ (-α) + (2 * (k : ℝ)) ^ (-α)) +
            C_out * (2 * (k : ℝ)) ^ (-α) :=
          add_le_add
            (mul_le_mul_of_nonneg_left (add_le_add hr1 hr2) hC_rem_nonneg)
            (mul_le_mul_of_nonneg_left hr4 hC_out_nonneg)
      _ ≤ C_large * (2 * (k : ℝ)) ^ (-α) := by
          dsimp [C_large]
          nlinarith
  obtain ⟨_, M_univ, hM_univ_pos, _, _, h_univ⟩ :=
    M.exists_uniform_laplaceSpinReal_bounds corr hν hΔ hM hgap h_ne hσ_le hσ_plus
  have h2Δ : 0 < 2 * Δ_phi := by positivity
  obtain ⟨C₁, hC₁_nonneg, hC₁⟩ :=
    exists_uniform_bound_tsum_pochhammerCoeff_sub h2Δ hσ_plus
  set C_id : ℝ := 2 * (4 : ℝ) ^ (2 * Δ_phi) * C₁
  have hC_id_nonneg : 0 ≤ C_id := by dsimp [C_id]; positivity
  set M_bd : ℝ := M_univ + C_id
  have hM_bd_pos : 0 < M_bd := by dsimp [M_bd]; positivity
  set C_bd : ℝ := max C_large (M_bd * (2 * (k₀ : ℝ)) ^ α)
  have hC_bd_pos : 0 < C_bd := lt_of_lt_of_le hC_large_pos (le_max_left _ _)
  refine ⟨M_bd, hM_bd_pos, C_bd, hC_bd_pos, fun {k} hk1 {σ} hσ => ?_⟩
  have hσ_neg : σ < 0 := lt_of_le_of_lt hσ.2 hσ_plus
  have h2k_ge1_nat : 1 ≤ 2 * k := by omega
  have h2k_ge1 : (1 : ℝ) ≤ 2 * (k : ℝ) := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    linarith
  have h2k_pos : (0 : ℝ) < 2 * (k : ℝ) := by linarith
  have h_id_sub_univ :
      |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityLaplaceReal Δ_phi (2 * k) σ -
        universalLaplaceReal Δ_phi σ| ≤ C_id := by
    have h_factor :
        (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityLaplaceReal Δ_phi (2 * k) σ -
          universalLaplaceReal Δ_phi σ =
        (2 * (4 : ℝ) ^ (2 * Δ_phi) * Real.exp (Δ_phi * σ)) *
          (((2 * k : ℕ) : ℝ) ^ (1 - 2 * Δ_phi) *
              (∑' n : ℕ, pochhammerCoeff (2 * Δ_phi) n *
                pochhammerCoeff (2 * Δ_phi) (n + 2 * k) * (Real.exp σ) ^ n) -
            (Real.Gamma (2 * Δ_phi))⁻¹ * (1 - Real.exp σ) ^ (- (2 * Δ_phi))) := by
      dsimp [identityLaplaceReal, universalLaplaceReal]
      push_cast
      ring
    rw [h_factor, abs_mul, abs_of_pos (by positivity)]
    have hexp_le1 : Real.exp (Δ_phi * σ) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hΔ_pos.le hσ_neg.le)
    have h_tsum_bd := hC₁ h2k_ge1_nat hσ.2
    have h_cast_r : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; rfl
    rw [h_cast_r] at h_tsum_bd ⊢
    have h_div_le : C₁ / (2 * (k : ℝ)) ≤ C₁ := div_le_self hC₁_nonneg h2k_ge1
    calc
      2 * (4 : ℝ) ^ (2 * Δ_phi) * Real.exp (Δ_phi * σ) *
          |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) *
              (∑' n : ℕ, pochhammerCoeff (2 * Δ_phi) n *
                pochhammerCoeff (2 * Δ_phi) (n + 2 * k) * (Real.exp σ) ^ n) -
            (Real.Gamma (2 * Δ_phi))⁻¹ * (1 - Real.exp σ) ^ (- (2 * Δ_phi))|
        ≤ (2 * (4 : ℝ) ^ (2 * Δ_phi) * 1) * C₁ :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left hexp_le1 (by positivity))
            (h_tsum_bd.trans h_div_le) (abs_nonneg _) (by positivity)
      _ = C_id := by dsimp [C_id]; ring
  have h_id_le :
      (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityLaplaceReal Δ_phi (2 * k) σ ≤
        universalLaplaceReal Δ_phi σ + C_id := by
    linarith [(abs_le.mp h_id_sub_univ).2]
  have h_sum_le :
      (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ +
        (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityLaplaceReal Δ_phi (2 * k) σ ≤ M_bd := by
    have h_u1 := (h_univ hk1 hσ).1
    dsimp [M_bd]
    linarith
  refine ⟨h_sum_le, ?_⟩
  rcases le_or_gt k₀ k with hk_ge | hk_lt
  · exact (h_large hk_ge hσ).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have h_L_nonneg :
        0 ≤ (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ :=
      mul_nonneg (by positivity) (M.laplaceSpinReal_nonneg _ _)
    have h_I_nonneg :
        0 ≤ (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityLaplaceReal Δ_phi (2 * k) σ :=
      mul_nonneg (by positivity) (identityLaplaceReal_nonneg hΔ_pos (2 * k) σ)
    have h_abs_le_M :
        |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ -
          (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityLaplaceReal Δ_phi (2 * k) σ| ≤ M_bd := by
      refine (abs_sub _ _).trans ?_
      rw [abs_of_nonneg h_L_nonneg, abs_of_nonneg h_I_nonneg]
      exact h_sum_le
    have h2k_le_2k₀ : 2 * (k : ℝ) ≤ 2 * (k₀ : ℝ) := by
      have : (k : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast hk_lt.le
      linarith
    have h_rpow_le : (2 * (k : ℝ)) ^ α ≤ (2 * (k₀ : ℝ)) ^ α :=
      Real.rpow_le_rpow h2k_pos.le h2k_le_2k₀ hα_pos.le
    have h_canc : (2 * (k : ℝ)) ^ α * (2 * (k : ℝ)) ^ (-α) = 1 := by
      rw [← Real.rpow_add h2k_pos, add_neg_cancel, Real.rpow_zero]
    have h_one_le : 1 ≤ (2 * (k₀ : ℝ)) ^ α * (2 * (k : ℝ)) ^ (-α) := by
      rw [← h_canc]
      exact mul_le_mul_of_nonneg_right h_rpow_le (by positivity)
    calc
      |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ -
          (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityLaplaceReal Δ_phi (2 * k) σ|
        ≤ M_bd * 1 := by linarith
      _ ≤ M_bd * ((2 * (k₀ : ℝ)) ^ α * (2 * (k : ℝ)) ^ (-α)) :=
          mul_le_mul_of_nonneg_left h_one_le hM_bd_pos.le
      _ = (M_bd * (2 * (k₀ : ℝ)) ^ α) * (2 * (k : ℝ)) ^ (-α) := by ring
      _ ≤ C_bd * (2 * (k : ℝ)) ^ (-α) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

end MonomialFourPointData

end CFT.LightconeBootstrap
