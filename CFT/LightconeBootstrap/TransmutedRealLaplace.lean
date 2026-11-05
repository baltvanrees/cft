/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Balt van Rees
-/
import CFT.LightconeBootstrap.LightconeBlockDecomp
import CFT.LightconeBootstrap.RealLaplaceBound

/-!
# Transmuted $t$-Channel Identity Laplace Transforms and Leading Crossing Factor

This file defines the transmuted universal and 1-term finite-spin $t$-channel identity Laplace
transforms (`transmutedUniversalLaplaceReal`, `transmutedIdentityLaplaceReal`), proves their
uniform $O(K^{-1})$ proximity (`exists_uniform_bound_transmutedIdentityLaplaceReal_sub_universal`)
for all $\Delta_\phi > 0$, and establishes basic regularity and modulus bounds for the leading
right-moving transmuted $t$-channel identity factor `crossFactorTransmuted` on $\operatorname{UcDisk}$.
-/

open Real Complex Topology Set Metric MeasureTheory Filter
open scoped BigOperators ENNReal

namespace CFT.LightconeBootstrap

/-! ## Section 1: Transmuted Universal & 1-Term $t$-Channel Identity Laplace Transforms -/

/-- The positive Gamma ratio $\frac{\Gamma(2\Delta_\phi)}{\Gamma(\Delta_\phi)^2} > 0$ relating the
transmuted primary normalization to the monomial normalization. -/
noncomputable def transmutedRatio (Δ_phi : ℝ) : ℝ :=
  Real.Gamma (2 * Δ_phi) / (Real.Gamma Δ_phi) ^ 2

lemma transmutedRatio_pos {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) :
    0 < transmutedRatio Δ_phi := by
  unfold transmutedRatio
  have h1 : 0 < Real.Gamma (2 * Δ_phi) := Real.Gamma_pos_of_pos (by positivity)
  have h2 : 0 < Real.Gamma Δ_phi := Real.Gamma_pos_of_pos hΔ
  positivity

/-- Leading-twist ($n = 0$, $h = \Delta_\phi$) universal GFF lightcone-block primary coefficient:
$$
C^{\text{GFF, LC}}_0(\Delta_\phi) := \frac{2 \cdot 4^{2\Delta_\phi}}{\Gamma(\Delta_\phi)^2}
  = \operatorname{transmutedRatio}(\Delta_\phi) \cdot
    \operatorname{universalCoeff}(\Delta_\phi, 0).
$$ -/
noncomputable def universalPrimaryLeadingCoeff (Δ_phi : ℝ) : ℝ :=
  2 * (4 : ℝ) ^ (2 * Δ_phi) / (Real.Gamma Δ_phi) ^ 2

lemma universalPrimaryLeadingCoeff_pos {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) :
    0 < universalPrimaryLeadingCoeff Δ_phi := by
  unfold universalPrimaryLeadingCoeff
  have h : 0 < Real.Gamma Δ_phi := Real.Gamma_pos_of_pos hΔ
  positivity

/-- The transmuted universal large-spin Laplace transform on the negative real axis $\sigma < 0$:
$$
\operatorname{transmutedUniversalLaplaceReal}(\Delta_\phi, \sigma) :=
  \frac{2 \cdot 4^{2\Delta_\phi}}{\Gamma(\Delta_\phi)^2} e^{\Delta_\phi \sigma}
    (1 - e^\sigma)^{-2\Delta_\phi}
  = \operatorname{transmutedRatio}(\Delta_\phi) \cdot
    \operatorname{universalLaplaceReal}(\Delta_\phi, \sigma).
$$ -/
noncomputable def transmutedUniversalLaplaceReal (Δ_phi σ : ℝ) : ℝ :=
  transmutedRatio Δ_phi * universalLaplaceReal Δ_phi σ

lemma transmutedUniversalLaplaceReal_eq (Δ_phi : ℝ) {σ : ℝ} (hΔ : 0 < Δ_phi) :
    transmutedUniversalLaplaceReal Δ_phi σ =
      universalPrimaryLeadingCoeff Δ_phi *
        Real.exp (Δ_phi * σ) * (1 - Real.exp σ) ^ (- (2 * Δ_phi)) := by
  dsimp [transmutedUniversalLaplaceReal, transmutedRatio, universalLaplaceReal,
    universalPrimaryLeadingCoeff]
  have hG : Real.Gamma (2 * Δ_phi) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  field_simp

lemma transmutedUniversalLaplaceReal_nonneg {Δ_phi σ : ℝ} (hΔ : 0 < Δ_phi) (hσ : σ < 0) :
    0 ≤ transmutedUniversalLaplaceReal Δ_phi σ :=
  mul_nonneg (transmutedRatio_pos hΔ).le (universalLaplaceReal_nonneg hΔ hσ)

/-- The 1-term finite-spin transmuted $t$-channel identity Laplace transform at spin $K = 2k$:
$$
\operatorname{transmutedIdentityLaplaceReal}(\Delta_\phi, K, \sigma) :=
  \frac{2 \cdot 4^{2\Delta_\phi} \Gamma(2\Delta_\phi + 1)}{\Gamma(\Delta_\phi)^2}
  e^{\Delta_\phi \sigma} \sum_{n=0}^{\infty} \frac{(2\Delta_\phi)_n}{n!}
    \frac{(2\Delta_\phi + 1)_{n + K}}{(n + K)!} e^{n \sigma}.
$$ -/
noncomputable def transmutedIdentityLaplaceReal (Δ_phi : ℝ) (K : ℕ) (σ : ℝ) : ℝ :=
  universalPrimaryLeadingCoeff Δ_phi * Real.Gamma (2 * Δ_phi + 1) * Real.exp (Δ_phi * σ) *
    ∑' n : ℕ, pochhammerCoeff (2 * Δ_phi) n * pochhammerCoeff (2 * Δ_phi + 1) (n + K) *
      (Real.exp σ) ^ n

lemma transmutedIdentityLaplaceReal_nonneg {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) (K : ℕ) (σ : ℝ) :
    0 ≤ transmutedIdentityLaplaceReal Δ_phi K σ := by
  unfold transmutedIdentityLaplaceReal
  have h1 : 0 < universalPrimaryLeadingCoeff Δ_phi := universalPrimaryLeadingCoeff_pos hΔ
  have h2 : 0 < Real.Gamma (2 * Δ_phi + 1) := Real.Gamma_pos_of_pos (by positivity)
  refine mul_nonneg (by positivity) (tsum_nonneg fun n => ?_)
  exact mul_nonneg
    (mul_nonneg (pochhammerCoeff_nonneg (by positivity) n)
      (pochhammerCoeff_nonneg (by positivity) (n + K)))
    (by positivity)

/-- **Uniform $O(K^{-1})$ Convergence of `transmutedIdentityLaplaceReal` to
`transmutedUniversalLaplaceReal` for All $\Delta_\phi > 0$**:
For every $\Delta_\phi > 0$ and $\sigma_+ < 0$, there exists $C \ge 0$ such that for all $K \ge 1$
and all $\sigma \le \sigma_+$,
$$
\left|K^{-2\Delta_\phi} \operatorname{transmutedIdentityLaplaceReal}(\Delta_\phi, K, \sigma)
  - \operatorname{transmutedUniversalLaplaceReal}(\Delta_\phi, \sigma)\right| \le \frac{C}{K}.
$$ -/
theorem exists_uniform_bound_transmutedIdentityLaplaceReal_sub_universal
    {Δ_phi σ_plus : ℝ} (hΔ : 0 < Δ_phi) (hσ_plus : σ_plus < 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : ℕ}, 1 ≤ K → ∀ {σ : ℝ}, σ ≤ σ_plus →
      |(K : ℝ) ^ (- (2 * Δ_phi)) * transmutedIdentityLaplaceReal Δ_phi K σ -
        transmutedUniversalLaplaceReal Δ_phi σ| ≤ C / (K : ℝ) := by
  have ha : 0 < 2 * Δ_phi := by positivity
  have hb : 0 < 2 * Δ_phi + 1 := by positivity
  obtain ⟨C₁, hC₁_nonneg, hC₁⟩ :=
    exists_uniform_bound_tsum_pochhammerCoeff_mixed_sub ha hb hσ_plus
  set pref : ℝ := universalPrimaryLeadingCoeff Δ_phi * Real.Gamma (2 * Δ_phi + 1)
  have hpref_pos : 0 < pref :=
    mul_pos (universalPrimaryLeadingCoeff_pos hΔ) (Real.Gamma_pos_of_pos hb)
  refine ⟨pref * C₁, mul_nonneg hpref_pos.le hC₁_nonneg, fun {K} hK {σ} hσ => ?_⟩
  have hσ_neg : σ < 0 := lt_of_le_of_lt hσ hσ_plus
  have h_exp_le1 : Real.exp (Δ_phi * σ) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hΔ.le hσ_neg.le)
  have h_pow : 1 - (2 * Δ_phi + 1) = - (2 * Δ_phi) := by ring
  have hG_ne : Real.Gamma (2 * Δ_phi + 1) ≠ 0 := (Real.Gamma_pos_of_pos hb).ne'
  have h_factor :
      (K : ℝ) ^ (- (2 * Δ_phi)) * transmutedIdentityLaplaceReal Δ_phi K σ -
        transmutedUniversalLaplaceReal Δ_phi σ =
      (pref * Real.exp (Δ_phi * σ)) *
        ((K : ℝ) ^ (1 - (2 * Δ_phi + 1)) *
            (∑' n : ℕ, pochhammerCoeff (2 * Δ_phi) n *
              pochhammerCoeff (2 * Δ_phi + 1) (n + K) * (Real.exp σ) ^ n) -
          (Real.Gamma (2 * Δ_phi + 1))⁻¹ * (1 - Real.exp σ) ^ (- (2 * Δ_phi))) := by
    rw [h_pow, transmutedUniversalLaplaceReal_eq Δ_phi hΔ]
    dsimp [transmutedIdentityLaplaceReal, pref]
    field_simp
  rw [h_factor, abs_mul, abs_of_pos (mul_pos hpref_pos (Real.exp_pos _))]
  calc
    pref * Real.exp (Δ_phi * σ) *
        |(K : ℝ) ^ (1 - (2 * Δ_phi + 1)) *
            (∑' n : ℕ, pochhammerCoeff (2 * Δ_phi) n *
              pochhammerCoeff (2 * Δ_phi + 1) (n + K) * (Real.exp σ) ^ n) -
          (Real.Gamma (2 * Δ_phi + 1))⁻¹ * (1 - Real.exp σ) ^ (- (2 * Δ_phi))|
      ≤ (pref * 1) * (C₁ / (K : ℝ)) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left h_exp_le1 hpref_pos.le)
          (hC₁ hK hσ) (abs_nonneg _) (mul_pos hpref_pos zero_lt_one).le
    _ = (pref * C₁) / (K : ℝ) := by ring

/-! ## Section 2: Leading Transmuted $t$-Channel Identity Factor on `UcDisk` -/

/-- The leading right-moving transmuted $t$-channel crossing factor on $\operatorname{UcDisk}$:
$$
\operatorname{crossFactorTransmuted}(\Delta_\phi, w) :=
  \frac{\Gamma(2\Delta_\phi + 1)}{\Gamma(\Delta_\phi)^2} \, 4^{\Delta_\phi} \,
  e^{\Delta_\phi w} (1 - e^w)^{-(2\Delta_\phi + 1)}.
$$ -/
noncomputable def crossFactorTransmuted (Δ_phi : ℝ) (w : ℂ) : ℂ :=
  ((Real.Gamma (2 * Δ_phi + 1) / (Real.Gamma Δ_phi) ^ 2 * (4 : ℝ) ^ Δ_phi : ℝ) : ℂ) *
    Complex.exp ((Δ_phi : ℂ) * w) * (1 - Complex.exp w) ^ (- ((2 * Δ_phi + 1 : ℝ) : ℂ))

lemma continuousOn_crossFactorTransmuted (Δ_phi : ℝ) :
    ContinuousOn (crossFactorTransmuted Δ_phi) UcDisk := by
  intro w hw
  have h_exp : DifferentiableAt ℂ (fun z => Complex.exp ((Δ_phi : ℂ) * z)) w :=
    (differentiableAt_id.const_mul (Δ_phi : ℂ)).cexp
  have h_sub : DifferentiableAt ℂ (fun z => 1 - Complex.exp z) w :=
    (differentiableAt_const 1).sub differentiableAt_id.cexp
  have h_cpow :
      DifferentiableAt ℂ
        (fun z => (1 - Complex.exp z) ^ (- ((2 * Δ_phi + 1 : ℝ) : ℂ))) w :=
    h_sub.cpow_const (one_sub_exp_mem_slitPlane hw)
  exact ((h_exp.const_mul _).mul h_cpow).continuousAt.continuousWithinAt

/-- Exact modulus of `crossFactorTransmuted Δ_phi w` for $w \in \operatorname{UcDisk}$. -/
theorem norm_crossFactorTransmuted_eq {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) {w : ℂ} (hw : w ∈ UcDisk) :
    ‖crossFactorTransmuted Δ_phi w‖ =
      (Real.Gamma (2 * Δ_phi + 1) / (Real.Gamma Δ_phi) ^ 2 * (4 : ℝ) ^ Δ_phi) *
        Real.exp (Δ_phi * w.re) * ‖1 - Complex.exp w‖ ^ (- (2 * Δ_phi + 1)) := by
  dsimp [crossFactorTransmuted]
  have hG1 : 0 < Real.Gamma (2 * Δ_phi + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hG2 : 0 < Real.Gamma Δ_phi := Real.Gamma_pos_of_pos hΔ
  rw [norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity), Complex.norm_exp]
  have hexp_re : ((Δ_phi : ℂ) * w).re = Δ_phi * w.re := by simp [Complex.mul_re]
  have h1q_ne : 1 - Complex.exp w ≠ 0 :=
    slitPlane_ne_zero (one_sub_exp_mem_slitPlane hw)
  have h1q :
      ‖(1 - Complex.exp w) ^ (- ((2 * Δ_phi + 1 : ℝ) : ℂ))‖ =
        ‖1 - Complex.exp w‖ ^ (- (2 * Δ_phi + 1)) := by
    rw [cpow_def_of_ne_zero h1q_ne, Complex.norm_exp]
    have hre : (Complex.log (1 - Complex.exp w) * -((2 * Δ_phi + 1 : ℝ) : ℂ)).re =
        Real.log ‖1 - Complex.exp w‖ * (- (2 * Δ_phi + 1)) := by
      simp [Complex.mul_re, Complex.log_re]
    rw [hre, Real.rpow_def_of_pos (norm_pos_iff.mpr h1q_ne)]
  rw [hexp_re, h1q]

/-- Upper bound on $\|\operatorname{crossFactorTransmuted}(\Delta_\phi, w)\|$ when
$\operatorname{Re}(w) \le a < 0$. -/
theorem norm_crossFactorTransmuted_le_of_re_le {Δ_phi a : ℝ} (hΔ : 0 < Δ_phi) (ha : a < 0)
    {w : ℂ} (hw : w ∈ UcDisk) (hwa : w.re ≤ a) :
    ‖crossFactorTransmuted Δ_phi w‖ ≤
      (Real.Gamma (2 * Δ_phi + 1) / (Real.Gamma Δ_phi) ^ 2 * (4 : ℝ) ^ Δ_phi) *
        (1 - Real.exp a) ^ (- (2 * Δ_phi + 1)) := by
  rw [norm_crossFactorTransmuted_eq hΔ hw]
  have hG1 : 0 < Real.Gamma (2 * Δ_phi + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hG2 : 0 < Real.Gamma Δ_phi := Real.Gamma_pos_of_pos hΔ
  have hexp_le1 : Real.exp (Δ_phi * w.re) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hΔ.le (hwa.trans ha.le))
  have h1a_pos : 0 < 1 - Real.exp a := sub_pos.mpr (Real.exp_lt_one_iff.mpr ha)
  have h1w_ge : 1 - Real.exp a ≤ ‖1 - Complex.exp w‖ := by
    calc
      1 - Real.exp a ≤ 1 - Real.exp w.re := sub_le_sub_left (Real.exp_le_exp.mpr hwa) 1
      _ = ‖(1 : ℂ)‖ - ‖Complex.exp w‖ := by rw [norm_one, Complex.norm_exp]
      _ ≤ ‖(1 : ℂ) - Complex.exp w‖ := norm_sub_norm_le 1 (Complex.exp w)
  have hrpow_le :
      ‖1 - Complex.exp w‖ ^ (- (2 * Δ_phi + 1)) ≤ (1 - Real.exp a) ^ (- (2 * Δ_phi + 1)) :=
    Real.rpow_le_rpow_of_nonpos h1a_pos h1w_ge (by linarith)
  calc
    (Real.Gamma (2 * Δ_phi + 1) / (Real.Gamma Δ_phi) ^ 2 * (4 : ℝ) ^ Δ_phi) *
        Real.exp (Δ_phi * w.re) * ‖1 - Complex.exp w‖ ^ (- (2 * Δ_phi + 1))
      ≤ (Real.Gamma (2 * Δ_phi + 1) / (Real.Gamma Δ_phi) ^ 2 * (4 : ℝ) ^ Δ_phi) * 1 *
          (1 - Real.exp a) ^ (- (2 * Δ_phi + 1)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hexp_le1 (by positivity))
          hrpow_le (by positivity) (by positivity)
    _ = (Real.Gamma (2 * Δ_phi + 1) / (Real.Gamma Δ_phi) ^ 2 * (4 : ℝ) ^ Δ_phi) *
          (1 - Real.exp a) ^ (- (2 * Δ_phi + 1)) := by ring

/-- Real binomial series expansion for the domination of `crossFactorTransmuted Δ_phi`. -/
lemma hasSum_exp_mul_one_sub_exp_rpow_neg_transmuted (Δ_phi : ℝ) {σ : ℝ} (hσ : σ < 0) :
    HasSum
      (fun m : ℕ =>
        pochhammerCoeff (2 * Δ_phi + 1) m * Real.exp ((Δ_phi + (m : ℝ)) * σ))
      (Real.exp (Δ_phi * σ) * (1 - Real.exp σ) ^ (- (2 * Δ_phi + 1))) := by
  have h_abs : |Real.exp σ| < 1 := by
    rw [abs_of_pos (Real.exp_pos σ)]
    exact Real.exp_lt_one_iff.mpr hσ
  have h_sum :=
    (hasSum_one_sub_rpow_neg (2 * Δ_phi + 1) h_abs).mul_left (Real.exp (Δ_phi * σ))
  refine h_sum.congr_fun fun m => ?_
  rw [← mul_left_comm, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 2
  ring

end CFT.LightconeBootstrap
