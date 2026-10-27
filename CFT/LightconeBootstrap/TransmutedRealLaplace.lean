/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Balt van Rees
-/
import CFT.LightconeBootstrap.LightconeBlockDecomp
import CFT.LightconeBootstrap.RealLaplaceBound

/-!
# Transmuted Crossing & Real-Axis Laplace Bounds for All $\Delta_\phi > 0$

This file implements **Phase 3** of `PLAN_CONFORMAL_BLOCKS.md`:
1. **Transmuted Universal & Exact $t$-Channel Identity Laplace Transforms
   (`transmutedUniversalLaplaceReal`, `transmutedIdentityLaplaceReal`)**:
   Under the 1D fractional transmutation operator $\mathcal{L}_0$ (`transmuteOp`), the right-moving
   $t$-channel identity singularity is boosted from $(1 - e^{w_r})^{-2\Delta_\phi}$ to
   $(1 - e^{w_r})^{-(2\Delta_\phi + 1)}$ while the left-moving singularity remains
   $(1 - e^{w_l})^{-2\Delta_\phi}$. Consequently, the spin-$K$ projection involves the mixed
   binomial series
   $$\sum_{n=0}^{\infty} \frac{(2\Delta_\phi)_n}{n!} \frac{(2\Delta_\phi + 1)_{n + K}}{(n + K)!}
     e^{n \sigma}$$
   with scaling power $K^{1 - (2\Delta_\phi + 1)} = K^{-2\Delta_\phi}$.
   Using `exists_uniform_bound_tsum_pochhammerCoeff_mixed_sub` from
   `CFT/LightconeBootstrap/RealLaplaceBound.lean`, we define the universal large-spin limit
   $$\operatorname{transmutedUniversalLaplaceReal}(\Delta_\phi, \sigma) :=
     \frac{2 \cdot 4^{2\Delta_\phi}}{\Gamma(\Delta_\phi)^2} e^{\Delta_\phi \sigma}
       (1 - e^\sigma)^{-2\Delta_\phi}
     = \frac{\Gamma(2\Delta_\phi)}{\Gamma(\Delta_\phi)^2}
       \operatorname{universalLaplaceReal}(\Delta_\phi, \sigma)$$
   and the exact finite-spin transmuted $t$-channel identity Laplace transform
   `transmutedIdentityLaplaceReal Δ_phi K σ`, and prove their uniform $O(K^{-1})$ proximity on
   $(-\infty, \sigma_+]$ (`exists_uniform_bound_transmutedIdentityLaplaceReal_sub_universal`) for
   **all** $\Delta_\phi > 0$.
2. **Uniform Real-Axis Laplace Bounds for All $\Delta_\phi > 0$
   (`LightconeBlockFourPointData.exists_uniform_transmuted_laplaceSpinReal_bounds`,
   `LightconeBlockFourPointData.exists_uniform_transmuted_laplaceSpinReal_sub_identity_bounds`)**:
   Because the transmuted spin-$2k$ normalization is $(2k)^{-2\Delta_\phi}$ rather than
   $(2k)^{1 - 2\Delta_\phi}$, the $O(1)$ outer contour contribution is suppressed by
   $(2k)^{-2\Delta_\phi}$, eliminating the $\Delta_\phi > 1/2$ barrier and yielding uniform
   real-axis Laplace bounds on every compact interval $[\sigma_-, \sigma_+] \subset (-\infty, 0)$
   for **all** $\Delta_\phi > 0$ and $h_{\text{gap}} > 0$ with exponent
   $\alpha = \min(2 h_{\text{gap}},\, 2\Delta_\phi) > 0$.
-/

open Real Complex Topology Set Metric MeasureTheory Filter
open scoped BigOperators ENNReal

namespace CFT.LightconeBootstrap

/-! ## Section 1: Transmuted Universal & Exact $t$-Channel Identity Laplace Transforms -/

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
$$C^{\text{GFF, LC}}_0(\Delta_\phi) := \frac{2 \cdot 4^{2\Delta_\phi}}{\Gamma(\Delta_\phi)^2}
  = \operatorname{transmutedRatio}(\Delta_\phi) \cdot
    \operatorname{universalCoeff}(\Delta_\phi, 0).$$ -/
noncomputable def universalPrimaryLeadingCoeff (Δ_phi : ℝ) : ℝ :=
  2 * (4 : ℝ) ^ (2 * Δ_phi) / (Real.Gamma Δ_phi) ^ 2

lemma universalPrimaryLeadingCoeff_pos {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) :
    0 < universalPrimaryLeadingCoeff Δ_phi := by
  unfold universalPrimaryLeadingCoeff
  have h : 0 < Real.Gamma Δ_phi := Real.Gamma_pos_of_pos hΔ
  positivity

/-- The transmuted universal large-spin Laplace transform on the negative real axis $\sigma < 0$:
$$\operatorname{transmutedUniversalLaplaceReal}(\Delta_\phi, \sigma) :=
  \frac{2 \cdot 4^{2\Delta_\phi}}{\Gamma(\Delta_\phi)^2} e^{\Delta_\phi \sigma}
    (1 - e^\sigma)^{-2\Delta_\phi}
  = \operatorname{transmutedRatio}(\Delta_\phi) \cdot
    \operatorname{universalLaplaceReal}(\Delta_\phi, \sigma).$$ -/
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

/-- The exact finite-spin transmuted $t$-channel identity Laplace transform at spin $K = 2k$:
$$\operatorname{transmutedIdentityLaplaceReal}(\Delta_\phi, K, \sigma) :=
  \frac{2 \cdot 4^{2\Delta_\phi} \Gamma(2\Delta_\phi + 1)}{\Gamma(\Delta_\phi)^2}
  e^{\Delta_\phi \sigma} \sum_{n=0}^{\infty} \frac{(2\Delta_\phi)_n}{n!}
    \frac{(2\Delta_\phi + 1)_{n + K}}{(n + K)!} e^{n \sigma}.$$ -/
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
$$\left|K^{-2\Delta_\phi} \operatorname{transmutedIdentityLaplaceReal}(\Delta_\phi, K, \sigma)
  - \operatorname{transmutedUniversalLaplaceReal}(\Delta_\phi, \sigma)\right| \le \frac{C}{K}.$$ -/
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

/-! ## Section 2: Transmuted Crossing & Remainder Hypothesis for All $\Delta_\phi > 0$ -/

namespace LightconeBlockFourPointData

variable (L : LightconeBlockFourPointData)

/-- **Transmuted $t$-Channel Crossing & Remainder Bound (`PLAN_CONFORMAL_BLOCKS.md`, Stage 3)**:
Under $\mathcal{L}_0$ (`transmuteOp`), the spin-$2k$ normalization factor is $(2k)^{-2\Delta_\phi}$,
and the Cauchy derivative bound on the $t$-channel remainder $R(w_l, w_r)$ along the folded contour
$w_r = -1/(2k) + i\theta$ ($\theta \in [-\pi/2, \pi/2]$) together with the outer contour
$\theta \in [-\pi, -\pi/2] \cup [\pi/2, \pi]$ bounds the difference between the rescaled spin-$2k$
transmuted Laplace transform and the exact transmuted $t$-channel identity Laplace transform by
$$O\bigl((2k)^{-2 h_{\text{gap}}} + (2k)^{-2\Delta_\phi}\bigr)$$
uniformly on every compact negative interval $[\sigma_-, \sigma_+] \subset (-\infty, 0)$ for
**all $\Delta_\phi > 0$ and $h_{\text{gap}} > 0$**. -/
structure HasTransmutedCrossingGap (Δ_phi : ℝ) : Prop where
  /-- Positivity of the external scaling dimension $\Delta_\phi > 0$ (no $\Delta_\phi > 1/2$
  restriction!). -/
  Δ_phi_pos : 0 < Δ_phi
  /-- Positivity of the $t$-channel non-identity twist gap $h_{\text{gap}} > 0$. -/
  h_gap_pos : 0 < L.h_gap
  /-- Uniform $t$-channel remainder and outer-contour bound on every compact negative interval
  $[\sigma_-, \sigma_+] \subset (-\infty, 0)$. -/
  exists_remainder_bound :
    ∀ {σ_minus σ_plus : ℝ}, σ_minus ≤ σ_plus → σ_plus < 0 →
      ∃ C_rem : ℝ, 0 ≤ C_rem ∧ ∀ {k : ℕ}, 1 ≤ k →
        ∀ {σ : ℝ}, σ ∈ Icc σ_minus σ_plus →
          |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
              L.toTransmutedMonomialFourPointData.laplaceSpinReal (2 * (k : ℤ)) σ -
            (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
              transmutedIdentityLaplaceReal Δ_phi (2 * k) σ| ≤
            C_rem * ((2 * (k : ℝ)) ^ (- (2 * L.h_gap)) + (2 * (k : ℝ)) ^ (- (2 * Δ_phi)))

/-- **Uniform Real-Axis Laplace Upper and Error Bounds Against the Exact Transmuted $t$-Channel
Identity (Valid for All $\Delta_\phi > 0$)**:
For any `LightconeBlockFourPointData` satisfying `HasTransmutedCrossingGap Δ_phi` and any compact
negative interval $[\sigma_-, \sigma_+] \subset (-\infty, 0)$, with
$$\alpha := \min(2 h_{\text{gap}},\, 2\Delta_\phi) > 0,$$
there exist constants $M_{\text{bd}} > 0$ and $C_{\text{bd}} > 0$ such that for all $k \ge 1$ and
all $\sigma \in [\sigma_-, \sigma_+]$:
1. $(2k)^{-2\Delta_\phi} \bigl(L^{\text{trans}}_{2k}(\sigma) +
     \operatorname{transmutedIdentityLaplaceReal}(\Delta_\phi, 2k, \sigma)\bigr) \le M_{\text{bd}}$,
2. $\bigl|(2k)^{-2\Delta_\phi} L^{\text{trans}}_{2k}(\sigma) -
     (2k)^{-2\Delta_\phi}
       \operatorname{transmutedIdentityLaplaceReal}(\Delta_\phi, 2k, \sigma)\bigr|
     \le C_{\text{bd}} \, (2k)^{-\alpha}$. -/
theorem exists_uniform_transmuted_laplaceSpinReal_sub_identity_bounds
    {Δ_phi : ℝ} (hcross : L.HasTransmutedCrossingGap Δ_phi)
    {σ_minus σ_plus : ℝ} (hσ_le : σ_minus ≤ σ_plus) (hσ_plus : σ_plus < 0) :
    let α := min (2 * L.h_gap) (2 * Δ_phi)
    0 < α ∧ ∃ M_bd > 0, ∃ C_bd > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {σ : ℝ}, σ ∈ Icc σ_minus σ_plus →
        (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
            L.toTransmutedMonomialFourPointData.laplaceSpinReal (2 * (k : ℤ)) σ +
          (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
            transmutedIdentityLaplaceReal Δ_phi (2 * k) σ ≤ M_bd ∧
        |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
            L.toTransmutedMonomialFourPointData.laplaceSpinReal (2 * (k : ℤ)) σ -
          (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
            transmutedIdentityLaplaceReal Δ_phi (2 * k) σ| ≤
          C_bd * (2 * (k : ℝ)) ^ (-α) := by
  intro α
  have hΔ : 0 < Δ_phi := hcross.Δ_phi_pos
  have hh_gap : 0 < L.h_gap := hcross.h_gap_pos
  have hα_pos : 0 < α := lt_min (by positivity) (by positivity)
  refine ⟨hα_pos, ?_⟩
  obtain ⟨C_rem, hC_rem_nonneg, hC_rem⟩ := hcross.exists_remainder_bound hσ_le hσ_plus
  obtain ⟨C_id, hC_id_nonneg, hC_id⟩ :=
    exists_uniform_bound_transmutedIdentityLaplaceReal_sub_universal hΔ hσ_plus
  have h1_exp_pos : 0 < 1 - Real.exp σ_plus :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr hσ_plus)
  set U_plus : ℝ :=
    universalPrimaryLeadingCoeff Δ_phi * (1 - Real.exp σ_plus) ^ (- (2 * Δ_phi))
  have hU_plus_pos : 0 < U_plus := by
    dsimp [U_plus]
    exact mul_pos (universalPrimaryLeadingCoeff_pos hΔ) (Real.rpow_pos_of_pos h1_exp_pos _)
  have h_univ_le : ∀ {σ : ℝ}, σ ∈ Icc σ_minus σ_plus →
      transmutedUniversalLaplaceReal Δ_phi σ ≤ U_plus := by
    intro σ hσ
    have hσ_neg : σ < 0 := lt_of_le_of_lt hσ.2 hσ_plus
    rw [transmutedUniversalLaplaceReal_eq Δ_phi hΔ]
    have hexp_le1 : Real.exp (Δ_phi * σ) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hΔ.le hσ_neg.le)
    have h1_sub_ge : 1 - Real.exp σ_plus ≤ 1 - Real.exp σ := by
      linarith [Real.exp_le_exp.mpr hσ.2]
    have hrpow_le : (1 - Real.exp σ) ^ (- (2 * Δ_phi)) ≤
        (1 - Real.exp σ_plus) ^ (- (2 * Δ_phi)) :=
      Real.rpow_le_rpow_of_nonpos h1_exp_pos h1_sub_ge (by linarith)
    have h1_exp_σ_pos : 0 < 1 - Real.exp σ := by linarith
    calc
      universalPrimaryLeadingCoeff Δ_phi * Real.exp (Δ_phi * σ) *
          (1 - Real.exp σ) ^ (- (2 * Δ_phi))
        ≤ (universalPrimaryLeadingCoeff Δ_phi * 1) *
            (1 - Real.exp σ_plus) ^ (- (2 * Δ_phi)) :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left hexp_le1 (universalPrimaryLeadingCoeff_pos hΔ).le)
            hrpow_le (Real.rpow_pos_of_pos h1_exp_σ_pos _).le
            (mul_pos (universalPrimaryLeadingCoeff_pos hΔ) zero_lt_one).le
      _ = U_plus := by dsimp [U_plus]; ring
  set C_bd : ℝ := 2 * C_rem + 1
  have hC_bd_pos : 0 < C_bd := by dsimp [C_bd]; positivity
  set M_bd : ℝ := 2 * (U_plus + C_id) + C_bd
  have hM_bd_pos : 0 < M_bd := by dsimp [M_bd]; positivity
  refine ⟨M_bd, hM_bd_pos, C_bd, hC_bd_pos, fun {k} hk1 {σ} hσ => ?_⟩
  have h2k_ge1_nat : 1 ≤ 2 * k := by omega
  have h2k_ge1 : (1 : ℝ) ≤ 2 * (k : ℝ) := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    linarith
  have h2k_pos : (0 : ℝ) < 2 * (k : ℝ) := by linarith
  have hr1 : (2 * (k : ℝ)) ^ (- (2 * L.h_gap)) ≤ (2 * (k : ℝ)) ^ (-α) := by
    refine Real.rpow_le_rpow_of_exponent_le h2k_ge1 ?_
    have : α ≤ 2 * L.h_gap := min_le_left _ _
    linarith
  have hr2 : (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) ≤ (2 * (k : ℝ)) ^ (-α) := by
    refine Real.rpow_le_rpow_of_exponent_le h2k_ge1 ?_
    have : α ≤ 2 * Δ_phi := min_le_right _ _
    linarith
  have h_err :
      |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
          L.toTransmutedMonomialFourPointData.laplaceSpinReal (2 * (k : ℤ)) σ -
        (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
          transmutedIdentityLaplaceReal Δ_phi (2 * k) σ| ≤
        C_bd * (2 * (k : ℝ)) ^ (-α) := by
    calc
      |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
          L.toTransmutedMonomialFourPointData.laplaceSpinReal (2 * (k : ℤ)) σ -
        (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
          transmutedIdentityLaplaceReal Δ_phi (2 * k) σ|
        ≤ C_rem * ((2 * (k : ℝ)) ^ (- (2 * L.h_gap)) + (2 * (k : ℝ)) ^ (- (2 * Δ_phi))) :=
          hC_rem hk1 hσ
      _ ≤ C_rem * ((2 * (k : ℝ)) ^ (-α) + (2 * (k : ℝ)) ^ (-α)) :=
          mul_le_mul_of_nonneg_left (add_le_add hr1 hr2) hC_rem_nonneg
      _ ≤ C_bd * (2 * (k : ℝ)) ^ (-α) := by
          dsimp [C_bd]
          have : 0 ≤ (2 * (k : ℝ)) ^ (-α) := by positivity
          nlinarith
  have h_id_bd :
      (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * transmutedIdentityLaplaceReal Δ_phi (2 * k) σ ≤
        U_plus + C_id := by
    have h_sub := hC_id h2k_ge1_nat hσ.2
    have h_cast : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; rfl
    rw [h_cast] at h_sub
    have h_div : C_id / (2 * (k : ℝ)) ≤ C_id := div_le_self hC_id_nonneg h2k_ge1
    have h_u := h_univ_le hσ
    linarith [(abs_le.mp (h_sub.trans h_div)).2]
  have hrpow_le1 : (2 * (k : ℝ)) ^ (-α) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos h2k_ge1 (by linarith)
  have h_err_le_C :
      |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
          L.toTransmutedMonomialFourPointData.laplaceSpinReal (2 * (k : ℤ)) σ -
        (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
          transmutedIdentityLaplaceReal Δ_phi (2 * k) σ| ≤ C_bd :=
    h_err.trans (by nlinarith)
  refine ⟨?_, h_err⟩
  dsimp [M_bd]
  linarith [(abs_le.mp h_err_le_C).2]

/-- **Uniform Real-Axis Laplace Upper and Error Bounds Against `transmutedUniversalLaplaceReal`
(Valid for All $\Delta_\phi > 0$)**:
Combining `exists_uniform_transmuted_laplaceSpinReal_sub_identity_bounds` with the $O((2k)^{-1})$
mixed-binomial convergence `exists_uniform_bound_transmutedIdentityLaplaceReal_sub_universal` yields
uniform upper and error bounds on $[\sigma_-, \sigma_+] \subset (-\infty, 0)$ for **all
$\Delta_\phi > 0$** with exponent
$$\alpha_{\text{univ}} := \min(2 h_{\text{gap}},\, \min 1\, (2\Delta_\phi)) > 0.$$ -/
theorem exists_uniform_transmuted_laplaceSpinReal_bounds
    {Δ_phi : ℝ} (hcross : L.HasTransmutedCrossingGap Δ_phi)
    {σ_minus σ_plus : ℝ} (hσ_le : σ_minus ≤ σ_plus) (hσ_plus : σ_plus < 0) :
    let α := min (2 * L.h_gap) (min 1 (2 * Δ_phi))
    0 < α ∧ ∃ M_bd > 0, ∃ C_bd > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {σ : ℝ}, σ ∈ Icc σ_minus σ_plus →
        (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
            L.toTransmutedMonomialFourPointData.laplaceSpinReal (2 * (k : ℤ)) σ +
          transmutedUniversalLaplaceReal Δ_phi σ ≤ M_bd ∧
        |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
            L.toTransmutedMonomialFourPointData.laplaceSpinReal (2 * (k : ℤ)) σ -
          transmutedUniversalLaplaceReal Δ_phi σ| ≤
          C_bd * (2 * (k : ℝ)) ^ (-α) := by
  intro α
  have hΔ : 0 < Δ_phi := hcross.Δ_phi_pos
  have hh_gap : 0 < L.h_gap := hcross.h_gap_pos
  have hα_pos : 0 < α := lt_min (by positivity) (lt_min zero_lt_one (by positivity))
  refine ⟨hα_pos, ?_⟩
  obtain ⟨_, M_id, hM_id_pos, C_id, hC_id_pos, h_id⟩ :=
    L.exists_uniform_transmuted_laplaceSpinReal_sub_identity_bounds hcross hσ_le hσ_plus
  obtain ⟨C_u, hC_u_nonneg, hC_u⟩ :=
    exists_uniform_bound_transmutedIdentityLaplaceReal_sub_universal hΔ hσ_plus
  refine ⟨M_id + C_u, by positivity, C_id + C_u, by positivity, fun {k} hk1 {σ} hσ => ?_⟩
  have h2k_ge1_nat : 1 ≤ 2 * k := by omega
  have h2k_ge1 : (1 : ℝ) ≤ 2 * (k : ℝ) := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    linarith
  have h2k_pos : (0 : ℝ) < 2 * (k : ℝ) := by linarith
  have h_sub_u := hC_u h2k_ge1_nat hσ.2
  have h_cast : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; rfl
  rw [h_cast] at h_sub_u
  have h_div_le1 : C_u / (2 * (k : ℝ)) ≤ C_u := div_le_self hC_u_nonneg h2k_ge1
  have h_u_le_id :
      transmutedUniversalLaplaceReal Δ_phi σ ≤
        (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * transmutedIdentityLaplaceReal Δ_phi (2 * k) σ + C_u := by
    linarith [(abs_le.mp (h_sub_u.trans h_div_le1)).1]
  have h_id_k := h_id hk1 hσ
  refine ⟨by linarith [h_id_k.1], ?_⟩
  let α_id := min (2 * L.h_gap) (2 * Δ_phi)
  have hα_le_id : α ≤ α_id :=
    min_le_min le_rfl (min_le_right 1 (2 * Δ_phi))
  have hα_le_one : α ≤ 1 :=
    (min_le_right _ _).trans (min_le_left 1 (2 * Δ_phi))
  have hr_id : (2 * (k : ℝ)) ^ (-α_id) ≤ (2 * (k : ℝ)) ^ (-α) :=
    Real.rpow_le_rpow_of_exponent_le h2k_ge1 (by linarith)
  have hr_one : (2 * (k : ℝ))⁻¹ ≤ (2 * (k : ℝ)) ^ (-α) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le h2k_ge1 (by linarith)
  have h_div_rpow : C_u / (2 * (k : ℝ)) ≤ C_u * (2 * (k : ℝ)) ^ (-α) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hr_one hC_u_nonneg
  calc
    |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
        L.toTransmutedMonomialFourPointData.laplaceSpinReal (2 * (k : ℤ)) σ -
      transmutedUniversalLaplaceReal Δ_phi σ|
      = |((2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
            L.toTransmutedMonomialFourPointData.laplaceSpinReal (2 * (k : ℤ)) σ -
          (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
            transmutedIdentityLaplaceReal Δ_phi (2 * k) σ) +
        ((2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
            transmutedIdentityLaplaceReal Δ_phi (2 * k) σ -
          transmutedUniversalLaplaceReal Δ_phi σ)| := by ring_nf
    _ ≤ |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
            L.toTransmutedMonomialFourPointData.laplaceSpinReal (2 * (k : ℤ)) σ -
          (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
            transmutedIdentityLaplaceReal Δ_phi (2 * k) σ| +
        |(2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
            transmutedIdentityLaplaceReal Δ_phi (2 * k) σ -
          transmutedUniversalLaplaceReal Δ_phi σ| := abs_add_le _ _
    _ ≤ C_id * (2 * (k : ℝ)) ^ (-α_id) + C_u / (2 * (k : ℝ)) :=
        add_le_add h_id_k.2 h_sub_u
    _ ≤ C_id * (2 * (k : ℝ)) ^ (-α) + C_u * (2 * (k : ℝ)) ^ (-α) :=
        add_le_add (mul_le_mul_of_nonneg_left hr_id hC_id_pos.le) h_div_rpow
    _ = (C_id + C_u) * (2 * (k : ℝ)) ^ (-α) := by ring

end LightconeBlockFourPointData

end CFT.LightconeBootstrap
