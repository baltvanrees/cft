/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Balt van Rees
-/
import CFT.LightconeBootstrap.TransmutedRealLaplace
import CFT.LightconeBootstrap.QuantitativeLargeSpin

/-!
# Quantitative Large-Spin Bootstrap for $d$-Dimensional Primary Operators

This file implements **Phase 4** of `PLAN_CONFORMAL_BLOCKS.md`, combining the Laplace-to-$C_c^2$
Tauberian theorem (`CFT/Analysis/LaplaceTauberian.lean`), the lightcone block transmutation
reduction (`CFT/LightconeBootstrap/LightconeBlockDecomp.lean`), and the transmuted real-axis
Laplace bounds (`CFT/LightconeBootstrap/TransmutedRealLaplace.lean`) to establish the quantitative
large-spin lightcone bootstrap for **$d$-dimensional primary operators** valid for **all
$\Delta_\phi > 0$ and $h_{\text{gap}} > 0$**:

1. **Transmuted Tauberian Theorems for All $\Delta_\phi > 0$
   (`exists_const_abs_transmuted_pairSpin_sub_identity_le`,
   `exists_const_abs_transmuted_pairSpin_sub_universal_le`)**:
   - Retaining the exact finite-spin transmuted $t$-channel identity coefficients in
     `transmutedIdentityPairing Δ_phi (2k) φ` gives the sharp exponent range
     $$0 < \gamma < \min(2 h_{\text{gap}},\, 2\Delta_\phi)$$
     for **all $\Delta_\phi > 0$** (completely eliminating the $\Delta_\phi > 1/2$ barrier!).
   - Comparing against the asymptotic Gamma limit `transmutedUniversalPairing Δ_phi φ` gives the
     exponent range $0 < \gamma < \min(2 h_{\text{gap}},\, \min 1\, (2\Delta_\phi))$.

2. **Leading-Twist ($M = 0$, $h \approx \Delta_\phi$) $d$-Dimensional Primary Bootstrap Theorems
   (`exists_const_abs_primary_leadingTwist_sub_identity_le`,
   `exists_const_abs_primary_leadingTwist_sub_universal_le`,
   `exists_const_abs_primary_pair_div_sub_identity_le`)**:
   For test functions $\varphi \in C_c^2([-N, N])$ supported below the first lightcone descendant
   threshold $\min(h_{\text{gap}} + 1,\, \Delta_\phi + 1)$:
   - All $m \ge 1$ subleading lightcone levels vanish on the support of $\varphi$, isolating the
     leading-twist $d$-dimensional primary measure $C_{0, 2k} \, \mu^{\text{prim}}_{2k}$,
   - All $n \ge 1$ higher double-twist families $\Delta_\phi + n$ vanish on the support of
     $\varphi$, isolating the $n = 0$ double-twist primary family at $h = \Delta_\phi$ with
     universal coefficient
     $$C^{\text{GFF, LC}}_0(\Delta_\phi) = \frac{2 \cdot 4^{2\Delta_\phi}}{\Gamma(\Delta_\phi)^2}.$$
-/

open MeasureTheory Set Filter Metric Real Complex Topology
open scoped BigOperators ENNReal

namespace CFT.LightconeBootstrap

/-! ## Section 1: Transmuted Universal Pairing & Shifted Measure -/

/-- The transmuted universal double-twist pairing for external dimension $\Delta_\phi$:
$$\operatorname{transmutedUniversalPairing}(\Delta_\phi, \varphi) :=
  \frac{2 \cdot 4^{2\Delta_\phi}}{\Gamma(\Delta_\phi)^2}
    \sum_{n=0}^{\infty} \frac{(2\Delta_\phi)_n}{n!} \varphi(\Delta_\phi + n)
  = \operatorname{transmutedRatio}(\Delta_\phi) \cdot
    \operatorname{universalMonomialPairing}(\Delta_\phi, \varphi).$$ -/
noncomputable def transmutedUniversalPairing (Δ_phi : ℝ) (φ : ℝ → ℝ) : ℝ :=
  transmutedRatio Δ_phi * universalMonomialPairing Δ_phi φ

/-- When $\varphi$ vanishes on $[\Delta_\phi + 1, \infty)$, all $n \ge 1$ terms in
`universalMonomialPairing Δ_phi φ` vanish, leaving only the $n = 0$ term at $h = \Delta_\phi$. -/
lemma universalMonomialPairing_eq_of_support_leadingTwist (Δ_phi : ℝ) {φ : ℝ → ℝ}
    (hφ_supp : ∀ h : ℝ, Δ_phi + 1 ≤ h → φ h = 0) :
    universalMonomialPairing Δ_phi φ =
      (2 * (4 : ℝ) ^ (2 * Δ_phi) / Real.Gamma (2 * Δ_phi)) * φ Δ_phi := by
  dsimp [universalMonomialPairing]
  rw [tsum_eq_single 0]
  · simp [realPochhammer_zero]
  · intro n hn
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have h_ge : Δ_phi + 1 ≤ Δ_phi + (n : ℝ) := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      linarith
    rw [hφ_supp (Δ_phi + (n : ℝ)) h_ge, mul_zero]

/-- On the leading-twist window $(-\infty, \Delta_\phi + 1)$, `transmutedUniversalPairing Δ_phi φ`
isolates the $n = 0$ double-twist primary value:
$$\operatorname{transmutedUniversalPairing}(\Delta_\phi, \varphi) =
  \frac{2 \cdot 4^{2\Delta_\phi}}{\Gamma(\Delta_\phi)^2} \varphi(\Delta_\phi).$$ -/
theorem transmutedUniversalPairing_eq_of_support_leadingTwist {Δ_phi : ℝ} (hΔ : 0 < Δ_phi)
    {φ : ℝ → ℝ} (hφ_supp : ∀ h : ℝ, Δ_phi + 1 ≤ h → φ h = 0) :
    transmutedUniversalPairing Δ_phi φ = universalPrimaryLeadingCoeff Δ_phi * φ Δ_phi := by
  dsimp [transmutedUniversalPairing]
  rw [universalMonomialPairing_eq_of_support_leadingTwist Δ_phi hφ_supp]
  dsimp [transmutedRatio, universalPrimaryLeadingCoeff]
  have hG : Real.Gamma (2 * Δ_phi) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  field_simp

/-- The transmuted universal shifted double-twist measure on $u = h - \Delta_\phi \in \mathbb{R}$,
supported on $\mathbb{N} \subset \mathbb{Z}$. -/
noncomputable def transmutedUniversalShiftedMeasure (Δ_phi : ℝ) : Measure ℝ :=
  ENNReal.ofReal (transmutedRatio Δ_phi) • universalShiftedMeasure Δ_phi

lemma transmutedUniversalShiftedMeasure_compl_intCast_eq_zero (Δ_phi : ℝ) :
    transmutedUniversalShiftedMeasure Δ_phi (univ \ range (Int.cast : ℤ → ℝ)) = 0 := by
  dsimp [transmutedUniversalShiftedMeasure]
  rw [universalShiftedMeasure_compl_intCast_eq_zero, mul_zero]

lemma integrable_exp_transmutedUniversalShiftedMeasure {Δ_phi σ : ℝ}
    (hΔ : 0 < Δ_phi) (hσ : σ < 0) :
    Integrable (fun u : ℝ => Real.exp (σ * u)) (transmutedUniversalShiftedMeasure Δ_phi) :=
  (integrable_exp_universalShiftedMeasure hΔ hσ).smul_measure ENNReal.ofReal_ne_top

lemma laplaceTransformReal_transmutedUniversalShiftedMeasure {Δ_phi σ : ℝ}
    (hΔ : 0 < Δ_phi) (hσ : σ < 0) :
    laplaceTransformReal (transmutedUniversalShiftedMeasure Δ_phi) σ =
      Real.exp (-Δ_phi * σ) * transmutedUniversalLaplaceReal Δ_phi σ := by
  dsimp [laplaceTransformReal, transmutedUniversalShiftedMeasure, transmutedUniversalLaplaceReal]
  rw [integral_smul_measure, ENNReal.toReal_ofReal (transmutedRatio_pos hΔ).le, smul_eq_mul]
  have h_u := laplaceTransformReal_universalShiftedMeasure hΔ hσ
  dsimp [laplaceTransformReal] at h_u
  rw [h_u]
  ring

lemma integral_shiftedTest_transmutedUniversalShiftedMeasure {Δ_phi : ℝ} (hΔ : 0 < Δ_phi)
    (N : ℕ) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hsupp : ∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) :
    ∫ u : ℝ, shiftedTest Δ_phi φ u ∂(transmutedUniversalShiftedMeasure Δ_phi) =
      transmutedUniversalPairing Δ_phi φ := by
  dsimp [transmutedUniversalShiftedMeasure, transmutedUniversalPairing]
  rw [integral_smul_measure, ENNReal.toReal_ofReal (transmutedRatio_pos hΔ).le, smul_eq_mul,
    integral_shiftedTest_universalShiftedMeasure hΔ N hφ hsupp]

/-! ## Section 2: Exact Finite-Spin Transmuted $t$-Channel Identity Measure -/

/-- Exact finite-spin transmuted $t$-channel identity pairing at spin $K = 2k$:
$$\operatorname{transmutedIdentityPairing}(\Delta_\phi, K, \varphi) :=
  \frac{2 \cdot 4^{2\Delta_\phi} \Gamma(2\Delta_\phi + 1)}{\Gamma(\Delta_\phi)^2}
  \sum_{n=0}^{\infty} \frac{(2\Delta_\phi)_n}{n!} \frac{(2\Delta_\phi + 1)_{n + K}}{(n + K)!}
    \varphi(\Delta_\phi + n).$$ -/
noncomputable def transmutedIdentityPairing (Δ_phi : ℝ) (K : ℕ) (φ : ℝ → ℝ) : ℝ :=
  universalPrimaryLeadingCoeff Δ_phi * Real.Gamma (2 * Δ_phi + 1) *
    ∑' n : ℕ, pochhammerCoeff (2 * Δ_phi) n * pochhammerCoeff (2 * Δ_phi + 1) (n + K) *
      φ (Δ_phi + (n : ℝ))

/-- Exact finite-spin leading-twist ($n = 0$) transmuted $t$-channel identity coefficient at
spin $K = 2k$:
$$\operatorname{transmutedIdentityLeadingCoeff}(\Delta_\phi, K) :=
  \frac{2 \cdot 4^{2\Delta_\phi} \Gamma(2\Delta_\phi + 1)}{\Gamma(\Delta_\phi)^2}
    \frac{(2\Delta_\phi + 1)_K}{K!}.$$ -/
noncomputable def transmutedIdentityLeadingCoeff (Δ_phi : ℝ) (K : ℕ) : ℝ :=
  universalPrimaryLeadingCoeff Δ_phi * Real.Gamma (2 * Δ_phi + 1) *
    pochhammerCoeff (2 * Δ_phi + 1) K

/-- When $\varphi$ vanishes on $[\Delta_\phi + 1, \infty)$, `transmutedIdentityPairing Δ_phi K φ`
collapses to its $n = 0$ term at $h = \Delta_\phi$. -/
theorem transmutedIdentityPairing_eq_of_support_leadingTwist (Δ_phi : ℝ) (K : ℕ) {φ : ℝ → ℝ}
    (hφ_supp : ∀ h : ℝ, Δ_phi + 1 ≤ h → φ h = 0) :
    transmutedIdentityPairing Δ_phi K φ = transmutedIdentityLeadingCoeff Δ_phi K * φ Δ_phi := by
  dsimp [transmutedIdentityPairing, transmutedIdentityLeadingCoeff]
  rw [tsum_eq_single 0]
  · simp [pochhammerCoeff, realPochhammer_zero]
    ring
  · intro n hn
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have h_ge : Δ_phi + 1 ≤ Δ_phi + (n : ℝ) := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      linarith
    rw [hφ_supp (Δ_phi + (n : ℝ)) h_ge, mul_zero]

/-- Rescaled weight of the $n$-th double-twist atom of the exact transmuted $t$-channel identity at
spin $2k$. -/
noncomputable def transmutedIdentityRescaledCoeff (Δ_phi : ℝ) (k n : ℕ) : ℝ :=
  (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
    (universalPrimaryLeadingCoeff Δ_phi * Real.Gamma (2 * Δ_phi + 1)) *
    pochhammerCoeff (2 * Δ_phi) n * pochhammerCoeff (2 * Δ_phi + 1) (n + 2 * k)

lemma transmutedIdentityRescaledCoeff_nonneg {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) (k n : ℕ) :
    0 ≤ transmutedIdentityRescaledCoeff Δ_phi k n := by
  unfold transmutedIdentityRescaledCoeff
  have h1 : 0 < universalPrimaryLeadingCoeff Δ_phi := universalPrimaryLeadingCoeff_pos hΔ
  have h2 : 0 < Real.Gamma (2 * Δ_phi + 1) := Real.Gamma_pos_of_pos (by positivity)
  exact mul_nonneg
    (mul_nonneg (by positivity) (pochhammerCoeff_nonneg (by positivity) n))
    (pochhammerCoeff_nonneg (by positivity) (n + 2 * k))

/-- Exact finite-spin transmuted $t$-channel identity shifted measure on $\mathbb{R}$, supported on
$\mathbb{N} \subset \mathbb{Z}$. -/
noncomputable def transmutedIdentityShiftedMeasure (Δ_phi : ℝ) (k : ℕ) : Measure ℝ :=
  natShiftedMeasure (transmutedIdentityRescaledCoeff Δ_phi k)

lemma transmutedIdentityShiftedMeasure_compl_intCast_eq_zero (Δ_phi : ℝ) (k : ℕ) :
    transmutedIdentityShiftedMeasure Δ_phi k (univ \ range (Int.cast : ℤ → ℝ)) = 0 :=
  natShiftedMeasure_compl_intCast_eq_zero _

lemma hasSum_transmutedIdentityRescaledCoeff_mul_exp {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) (k : ℕ)
    {σ : ℝ} (hσ : σ < 0) :
    HasSum (fun n : ℕ => transmutedIdentityRescaledCoeff Δ_phi k n * Real.exp (σ * (n : ℝ)))
      (Real.exp (-Δ_phi * σ) *
        ((2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * transmutedIdentityLaplaceReal Δ_phi (2 * k) σ)) := by
  have ha : 0 < 2 * Δ_phi := by positivity
  have hb : 0 < 2 * Δ_phi + 1 := by positivity
  have h_sum := (summable_pochhammerCoeff_mixed_mul_exp ha hb (2 * k) hσ).hasSum.mul_left
    ((2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
      (universalPrimaryLeadingCoeff Δ_phi * Real.Gamma (2 * Δ_phi + 1)))
  have h_target :
      ((2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
          (universalPrimaryLeadingCoeff Δ_phi * Real.Gamma (2 * Δ_phi + 1))) *
        (∑' n : ℕ, pochhammerCoeff (2 * Δ_phi) n * pochhammerCoeff (2 * Δ_phi + 1) (n + 2 * k) *
          (Real.exp σ) ^ n) =
        Real.exp (-Δ_phi * σ) *
          ((2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * transmutedIdentityLaplaceReal Δ_phi (2 * k) σ) := by
    dsimp [transmutedIdentityLaplaceReal]
    have hexp_canc : Real.exp (-Δ_phi * σ) * Real.exp (Δ_phi * σ) = 1 := by
      rw [← Real.exp_add]
      have : -Δ_phi * σ + Δ_phi * σ = 0 := by ring
      rw [this, Real.exp_zero]
    linear_combination
      -(((2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
          (universalPrimaryLeadingCoeff Δ_phi * Real.Gamma (2 * Δ_phi + 1))) *
        (∑' n : ℕ, pochhammerCoeff (2 * Δ_phi) n * pochhammerCoeff (2 * Δ_phi + 1) (n + 2 * k) *
          (Real.exp σ) ^ n)) * hexp_canc
  rw [h_target] at h_sum
  refine h_sum.congr_fun fun n => ?_
  dsimp [transmutedIdentityRescaledCoeff]
  rw [← Real.exp_nat_mul]
  ring_nf

lemma integrable_exp_transmutedIdentityShiftedMeasure {Δ_phi σ : ℝ}
    (hΔ : 0 < Δ_phi) (k : ℕ) (hσ : σ < 0) :
    Integrable (fun u : ℝ => Real.exp (σ * u)) (transmutedIdentityShiftedMeasure Δ_phi k) :=
  integrable_exp_natShiftedMeasure (transmutedIdentityRescaledCoeff_nonneg hΔ k)
    (hasSum_transmutedIdentityRescaledCoeff_mul_exp hΔ k hσ)

lemma laplaceTransformReal_transmutedIdentityShiftedMeasure {Δ_phi σ : ℝ}
    (hΔ : 0 < Δ_phi) (k : ℕ) (hσ : σ < 0) :
    laplaceTransformReal (transmutedIdentityShiftedMeasure Δ_phi k) σ =
      Real.exp (-Δ_phi * σ) *
        ((2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * transmutedIdentityLaplaceReal Δ_phi (2 * k) σ) :=
  laplaceTransformReal_natShiftedMeasure (transmutedIdentityRescaledCoeff_nonneg hΔ k)
    (hasSum_transmutedIdentityRescaledCoeff_mul_exp hΔ k hσ)

lemma integral_shiftedTest_transmutedIdentityShiftedMeasure {Δ_phi : ℝ} (hΔ : 0 < Δ_phi)
    (k N : ℕ) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hsupp : ∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) :
    ∫ u : ℝ, shiftedTest Δ_phi φ u ∂(transmutedIdentityShiftedMeasure Δ_phi k) =
      (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * transmutedIdentityPairing Δ_phi (2 * k) φ := by
  unfold transmutedIdentityShiftedMeasure transmutedIdentityPairing
  rw [integral_shiftedTest_natShiftedMeasure
    (transmutedIdentityRescaledCoeff_nonneg hΔ k) Δ_phi N hφ hsupp]
  dsimp [transmutedIdentityRescaledCoeff]
  simp_rw [mul_assoc]
  rw [tsum_mul_left, tsum_mul_left, tsum_mul_left]

/-! ## Section 3: Transmuted Spin-$2k$ Shifted Measure & Main Primary Bootstrap Theorems -/

namespace LightconeBlockFourPointData

variable (L : LightconeBlockFourPointData)

/-- **Quantitative Transmuted Lightcone Bootstrap Against the Exact Transmuted $t$-Channel Identity
(Valid for All $\Delta_\phi > 0$ and $0 < \gamma < \min(2 h_{\text{gap}},\, 2\Delta_\phi)$)**:
For any `LightconeBlockFourPointData` satisfying `HasTransmutedCrossingGap Δ_phi`, every support
bound $N \in \mathbb{N}$, and every target exponent
$$0 < \gamma < \min(2 h_{\text{gap}},\, 2\Delta_\phi),$$
there exists $C > 0$ such that for all $k \ge 1$ and all twice-differentiable test functions
$\varphi : \mathbb{R} \to \mathbb{R}$ supported in $[-N, N]$ with
$|\varphi|, |\varphi'|, |\varphi''| \le M_\varphi$:
$$\Bigl|(2k)^{-2\Delta_\phi} L.\text{toTransmutedMonomialFourPointData.pairSpin } (2k)\ \varphi -
  (2k)^{-2\Delta_\phi} \operatorname{transmutedIdentityPairing}(\Delta_\phi, 2k, \varphi)\Bigr|
  \le C \, (2k)^{-\gamma} \, M_\varphi.$$ -/
theorem exists_const_abs_transmuted_pairSpin_sub_identity_le {Δ_phi γ : ℝ}
    (hcross : L.HasTransmutedCrossingGap Δ_phi)
    (hγ_pos : 0 < γ) (hγ_lt : γ < min (2 * L.h_gap) (2 * Δ_phi))
    (N : ℕ) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      Differentiable ℝ φ → Differentiable ℝ (deriv φ) →
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      0 ≤ M_φ →
      (∀ h, |φ h| ≤ M_φ) → (∀ h, |deriv φ h| ≤ M_φ) →
      (∀ h, |deriv (deriv φ) h| ≤ M_φ) →
      |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
          L.toTransmutedMonomialFourPointData.pairSpin (2 * (k : ℤ)) φ -
        (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
          transmutedIdentityPairing Δ_phi (2 * k) φ| ≤
        C * (2 * (k : ℝ)) ^ (-γ) * M_φ := by
  have hΔ_pos : 0 < Δ_phi := hcross.Δ_phi_pos
  set α : ℝ := min (2 * L.h_gap) (2 * Δ_phi)
  have hα_pos : 0 < α := lt_trans hγ_pos hγ_lt
  obtain ⟨A, hA, hθ_ge⟩ := exists_gt_one_le_mul_midpointHarmonicExp hα_pos hγ_lt
  obtain ⟨_, M_raw, hM_raw_pos, C_raw, hC_raw_pos, h_raw⟩ :=
    L.exists_uniform_transmuted_laplaceSpinReal_sub_identity_bounds hcross
      (by linarith : 1 - 2 * A ≤ -1) (by norm_num : (-1 : ℝ) < 0)
  exact L.toTransmutedMonomialFourPointData.exists_const_abs_rescaled_pairSpin_sub_le
    hA hα_pos hθ_ge hM_raw_pos hC_raw_pos N
    (transmutedIdentityShiftedMeasure Δ_phi)
    (fun k σ => (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * transmutedIdentityLaplaceReal Δ_phi (2 * k) σ)
    (fun k φ => (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * transmutedIdentityPairing Δ_phi (2 * k) φ)
    (transmutedIdentityShiftedMeasure_compl_intCast_eq_zero Δ_phi)
    (fun k _ hσ => integrable_exp_transmutedIdentityShiftedMeasure hΔ_pos k hσ)
    (fun k _ hσ => laplaceTransformReal_transmutedIdentityShiftedMeasure hΔ_pos k hσ)
    (fun k _ _ =>
      mul_nonneg (by positivity) (transmutedIdentityLaplaceReal_nonneg hΔ_pos (2 * k) _))
    (fun k _ hφ hsupp => integral_shiftedTest_transmutedIdentityShiftedMeasure hΔ_pos k N hφ hsupp)
    (fun hk1 _ hσ => h_raw hk1 hσ)

/-- **Quantitative Transmuted Lightcone Bootstrap Against `transmutedUniversalPairing`**
(Valid for All $\Delta_\phi > 0$ and
$0 < \gamma < \min(2 h_{\text{gap}},\, \min 1\, (2\Delta_\phi))$): -/
theorem exists_const_abs_transmuted_pairSpin_sub_universal_le {Δ_phi γ : ℝ}
    (hcross : L.HasTransmutedCrossingGap Δ_phi)
    (hγ_pos : 0 < γ) (hγ_lt : γ < min (2 * L.h_gap) (min 1 (2 * Δ_phi)))
    (N : ℕ) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      Differentiable ℝ φ → Differentiable ℝ (deriv φ) →
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      0 ≤ M_φ →
      (∀ h, |φ h| ≤ M_φ) → (∀ h, |deriv φ h| ≤ M_φ) →
      (∀ h, |deriv (deriv φ) h| ≤ M_φ) →
      |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
          L.toTransmutedMonomialFourPointData.pairSpin (2 * (k : ℤ)) φ -
        transmutedUniversalPairing Δ_phi φ| ≤
        C * (2 * (k : ℝ)) ^ (-γ) * M_φ := by
  have hΔ_pos : 0 < Δ_phi := hcross.Δ_phi_pos
  set α : ℝ := min (2 * L.h_gap) (min 1 (2 * Δ_phi))
  have hα_pos : 0 < α := lt_trans hγ_pos hγ_lt
  obtain ⟨A, hA, hθ_ge⟩ := exists_gt_one_le_mul_midpointHarmonicExp hα_pos hγ_lt
  obtain ⟨_, M_raw, hM_raw_pos, C_raw, hC_raw_pos, h_raw⟩ :=
    L.exists_uniform_transmuted_laplaceSpinReal_bounds hcross
      (by linarith : 1 - 2 * A ≤ -1) (by norm_num : (-1 : ℝ) < 0)
  exact L.toTransmutedMonomialFourPointData.exists_const_abs_rescaled_pairSpin_sub_le
    hA hα_pos hθ_ge hM_raw_pos hC_raw_pos N
    (fun _ => transmutedUniversalShiftedMeasure Δ_phi)
    (fun _ => transmutedUniversalLaplaceReal Δ_phi)
    (fun _ => transmutedUniversalPairing Δ_phi)
    (fun _ => transmutedUniversalShiftedMeasure_compl_intCast_eq_zero Δ_phi)
    (fun _ _ hσ => integrable_exp_transmutedUniversalShiftedMeasure hΔ_pos hσ)
    (fun _ _ hσ => laplaceTransformReal_transmutedUniversalShiftedMeasure hΔ_pos hσ)
    (fun _ _ hσ => transmutedUniversalLaplaceReal_nonneg hΔ_pos hσ)
    (fun _ _ hφ hsupp => integral_shiftedTest_transmutedUniversalShiftedMeasure hΔ_pos N hφ hsupp)
    (fun hk1 _ hσ => h_raw hk1 hσ)

/-- **Main Quantitative Leading-Twist ($M = 0$) $d$-Dimensional Primary Bootstrap Theorem Against
the Exact Transmuted $t$-Channel Identity**:
For **all $\Delta_\phi > 0$**, **all $h_{\text{gap}} > 0$**, and **all
$0 < \gamma < \min(2 h_{\text{gap}},\, 2\Delta_\phi)$**, there exists $C > 0$ such that for all
$k \ge 1$ and all twice-differentiable test functions $\varphi : \mathbb{R} \to \mathbb{R}$
supported in $[-N, N] \cap (-\infty, \min(h_{\text{gap}} + 1,\, \Delta_\phi + 1))$:
$$\left|(2k)^{-2\Delta_\phi} C_{0, 2k} \int_{\mathbb{R}}
    \operatorname{transmuteWeight}(h + 2k) \, \varphi(h) \, d\mu^{\text{prim}}_{2k}(h) -
  (2k)^{-2\Delta_\phi} \operatorname{transmutedIdentityLeadingCoeff}(\Delta_\phi, 2k) \,
    \varphi(\Delta_\phi)\right| \le C \, (2k)^{-\gamma} \, M_\varphi.$$ -/
theorem exists_const_abs_primary_leadingTwist_sub_identity_le {Δ_phi γ : ℝ}
    (hcross : L.HasTransmutedCrossingGap Δ_phi)
    (hγ_pos : 0 < γ) (hγ_lt : γ < min (2 * L.h_gap) (2 * Δ_phi))
    (N : ℕ) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      Differentiable ℝ φ → Differentiable ℝ (deriv φ) →
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      (∀ h : ℝ, L.h_gap + 1 ≤ h → φ h = 0) →
      (∀ h : ℝ, Δ_phi + 1 ≤ h → φ h = 0) →
      0 ≤ M_φ →
      (∀ h, |φ h| ≤ M_φ) → (∀ h, |deriv φ h| ≤ M_φ) →
      (∀ h, |deriv (deriv φ) h| ≤ M_φ) →
      |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * L.leadingTwistCoeff (2 * k) *
          (∫ h : ℝ, transmuteWeight (h + (2 * k : ℕ)) * φ h ∂(L.muPrim (2 * k))) -
        (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
          transmutedIdentityLeadingCoeff Δ_phi (2 * k) * φ Δ_phi| ≤
        C * (2 * (k : ℝ)) ^ (-γ) * M_φ := by
  obtain ⟨C, hC_pos, hC⟩ :=
    L.exists_const_abs_transmuted_pairSpin_sub_identity_le hcross hγ_pos hγ_lt N
  refine ⟨C, hC_pos,
    fun {k} hk1 {φ} {M_φ} hφ hφ' hsupp hsupp_gap hsupp_id hM_φ hφ0 hφ1 hφ2 => ?_⟩
  have h2k_ge1 : 1 ≤ 2 * k := by omega
  have h_pair := L.pairSpin_toTransmuted_eq_primary_of_support_leadingTwist h2k_ge1 hsupp_gap
  have h_cast : ((2 * k : ℕ) : ℤ) = 2 * (k : ℤ) := by push_cast; rfl
  rw [h_cast] at h_pair
  have h_id := transmutedIdentityPairing_eq_of_support_leadingTwist Δ_phi (2 * k) hsupp_id
  have h_bound := hC hk1 hφ hφ' hsupp hM_φ hφ0 hφ1 hφ2
  rw [h_pair, h_id] at h_bound
  simpa [mul_assoc] using h_bound

/-- **Main Quantitative Leading-Twist ($M = 0$) $d$-Dimensional Primary Bootstrap Theorem Against
the Universal GFF Limit**
$C^{\text{GFF, LC}}_0(\Delta_\phi) = \frac{2 \cdot 4^{2\Delta_\phi}}{\Gamma(\Delta_\phi)^2}$:
For **all $\Delta_\phi > 0$**, **all $h_{\text{gap}} > 0$**, and **all
$0 < \gamma < \min(2 h_{\text{gap}},\, \min 1\, (2\Delta_\phi))$**, there exists $C > 0$ such that
for all $k \ge 1$ and all twice-differentiable test functions $\varphi : \mathbb{R} \to \mathbb{R}$
supported in $[-N, N] \cap (-\infty, \min(h_{\text{gap}} + 1,\, \Delta_\phi + 1))$:
$$\left|(2k)^{-2\Delta_\phi} C_{0, 2k} \int_{\mathbb{R}}
    \operatorname{transmuteWeight}(h + 2k) \, \varphi(h) \, d\mu^{\text{prim}}_{2k}(h) -
  \frac{2 \cdot 4^{2\Delta_\phi}}{\Gamma(\Delta_\phi)^2} \, \varphi(\Delta_\phi)\right|
  \le C \, (2k)^{-\gamma} \, M_\varphi.$$ -/
theorem exists_const_abs_primary_leadingTwist_sub_universal_le {Δ_phi γ : ℝ}
    (hcross : L.HasTransmutedCrossingGap Δ_phi)
    (hγ_pos : 0 < γ) (hγ_lt : γ < min (2 * L.h_gap) (min 1 (2 * Δ_phi)))
    (N : ℕ) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      Differentiable ℝ φ → Differentiable ℝ (deriv φ) →
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      (∀ h : ℝ, L.h_gap + 1 ≤ h → φ h = 0) →
      (∀ h : ℝ, Δ_phi + 1 ≤ h → φ h = 0) →
      0 ≤ M_φ →
      (∀ h, |φ h| ≤ M_φ) → (∀ h, |deriv φ h| ≤ M_φ) →
      (∀ h, |deriv (deriv φ) h| ≤ M_φ) →
      |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * L.leadingTwistCoeff (2 * k) *
          (∫ h : ℝ, transmuteWeight (h + (2 * k : ℕ)) * φ h ∂(L.muPrim (2 * k))) -
        universalPrimaryLeadingCoeff Δ_phi * φ Δ_phi| ≤
        C * (2 * (k : ℝ)) ^ (-γ) * M_φ := by
  obtain ⟨C, hC_pos, hC⟩ :=
    L.exists_const_abs_transmuted_pairSpin_sub_universal_le hcross hγ_pos hγ_lt N
  refine ⟨C, hC_pos,
    fun {k} hk1 {φ} {M_φ} hφ hφ' hsupp hsupp_gap hsupp_id hM_φ hφ0 hφ1 hφ2 => ?_⟩
  have h2k_ge1 : 1 ≤ 2 * k := by omega
  have h_pair := L.pairSpin_toTransmuted_eq_primary_of_support_leadingTwist h2k_ge1 hsupp_gap
  have h_cast : ((2 * k : ℕ) : ℤ) = 2 * (k : ℤ) := by push_cast; rfl
  rw [h_cast] at h_pair
  have h_univ :=
    transmutedUniversalPairing_eq_of_support_leadingTwist hcross.Δ_phi_pos hsupp_id
  have h_bound := hC hk1 hφ hφ' hsupp hM_φ hφ0 hφ1 hφ2
  rw [h_pair, h_univ] at h_bound
  simpa [mul_assoc] using h_bound

end LightconeBlockFourPointData

end CFT.LightconeBootstrap
