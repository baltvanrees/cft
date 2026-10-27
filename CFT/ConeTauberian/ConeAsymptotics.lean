/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Balt van Rees
-/
import CFT.Analysis.Karamata2d
import CFT.ConeTauberian.ErdelyiKoberInversion
import CFT.ConeTauberian.Branching2d

/-!
# Quantitative High-Energy Tauberian Asymptotics for $d$-Dimensional Primary Operators

This file implements **Phase 4** of `CFT/ConeTauberian/PLAN.md`, combining the quantitative
two-variable Fourier-Laplace Tauberian theorem (`CFT/Analysis/Karamata2d.lean`), the
Erdélyi–Kober fractional integral and continuum primary density
(`CFT/ConeTauberian/ErdelyiKoberInversion.lean`), and the 2D block bilateral transmutation and
branching bounds (`CFT/ConeTauberian/Branching2d.lean`) to establish the three main theorems of
the module:

1. **Theorem 1A — Quantitative Non-Universal Bound Against the Exact $t$-Channel Identity
   (`exists_const_abs_transmuted2d_sub_identity_le`, `tendsto_transmuted2d_sub_identity`)**:
   For **all** $\Delta_\phi > 0$ and **all** $h_{\text{gap}} > 0$, comparing the rescaled 2D
   bilaterally transmuted OPE measure $\mu^{\text{trans}}_\Delta$ against the exact universal
   $t$-channel identity measure $\mu^{\text{id, trans}}_\Delta(\Delta_\phi)$ yields a power-law
   error bound $O(\Delta^{-\gamma})$ with exponent
   $\gamma = \frac{2 h_{\text{gap}}}{p_{\text{deg}} + 1} > 0$ controlled **purely by
   $2 h_{\text{gap}}$** (with no $\Delta^{-1}$ Stirling barrier and no $\Delta^{-2\Delta_\phi}$
   outer-contour barrier).

2. **Theorem 1B — Quantitative $O(\Delta^{-\gamma})$ Smoothed Primary Bootstrap Against the
   Continuum Density $\rho^{\text{prim}}_{\nu, \Delta_\phi}(u, \xi)$
   (`exists_const_abs_primaryCone_sub_le`, `tendsto_primaryConePairing`)**:
   Combining Theorem 1A with the universal $O(\Delta^{-1})$ Stirling and Erdélyi–Kober branching
   reduction yields the quantitative $O(\Delta^{-\gamma})$ bound for the unweighted primary OPE
   measure $d\mu_{\text{OPE}}(\Delta', \ell)$ paired with a smooth compactly supported test
   function $\chi(\Delta'/\Delta, \ell/\Delta')$, with exponent
   $\gamma = \min\bigl(\frac{2 h_{\text{gap}}}{p_{\text{deg}} + 1},\, 1\bigr) > 0$.

3. **Corollary 2 — Cumulative Spin-Summed Primary Asymptotics
   (`continuumPrimaryPairing_indicator_cylinder`, `tendsto_cumulativePrimaryWeight`)**:
   For $\nu > 0$ and $\Delta_\phi > \frac{\nu}{2} + \frac{1}{4}$, the continuum primary density
   $\rho^{\text{prim}}_{\nu, \Delta_\phi}(u, \xi)$ is integrable on the full unit cylinder
   $(0, 1)^2$ with integral $\mathcal{C}^{\text{prim}}_\nu(\Delta_\phi)$, and sandwiching the
   cylinder indicator between smooth test functions yields:
   $$\Delta^{2\nu - 4\Delta_\phi} \, \operatorname{cumulativePrimaryWeight}(D, \Delta)
     \;\underset{\Delta \to \infty}{\longrightarrow}\; \mathcal{C}^{\text{prim}}_\nu(\Delta_\phi).$$
-/

open MeasureTheory Set Filter Metric Real Complex Topology
open scoped BigOperators ENNReal

namespace CFT.ConeTauberian

/-! ## Section 1: `ConeBlockFourPointData` & Bilateral Transmuted Crossing Gap -/

/-- **Cone-Bootstrap Four-Point Spectral Data (`PLAN.md`, Stage 4)**:
packages the $d$-dimensional unweighted primary OPE spectral measure `μ_OPE` on $\mathbb{R} \times
\mathbb{N}$, the rescaled 2D bilaterally transmuted OPE measure `μ_trans2d Δ` on
$(u_l, u_r) = (h'/\Delta, \bar{h}'/\Delta) \in \mathbb{R}^2$ (normalized by
$\Delta^{-2 - 4\Delta_\phi}$), the exact universal rescaled 2D transmuted $t$-channel identity
measure `μ_id2d Δ` on $\mathbb{R}^2$, and the $t$-channel non-identity twist gap `h_gap`. -/
structure ConeBlockFourPointData (ν Δ_phi : ℝ) where
  /-- The unweighted $d$-dimensional primary OPE measure $d\mu_{\text{OPE}}(\Delta', \ell)$ on
  $\mathbb{R} \times \mathbb{N}$ (`corr.mu_measure`). -/
  μ_OPE : Measure (ℝ × ℕ)
  /-- For each $\Delta \ge 1$, the rescaled 2D bilaterally transmuted OPE measure on
  $(u_l, u_r) = (h'/\Delta, \bar{h}'/\Delta) \in \mathbb{R}^2$, normalized by
  $\Delta^{-2 - 4\Delta_\phi}$. -/
  μ_trans2d : ℝ → Measure (ℝ × ℝ)
  /-- For each $\Delta \ge 1$, the exact universal rescaled 2D bilaterally transmuted $t$-channel
  identity measure on $(u_l, u_r) \in \mathbb{R}^2$, normalized by $\Delta^{-2 - 4\Delta_\phi}$. -/
  μ_id2d : ℝ → Measure (ℝ × ℝ)
  /-- The $t$-channel non-identity twist gap $h_{\text{gap}} > 0$. -/
  h_gap : ℝ

namespace ConeBlockFourPointData

variable {ν Δ_phi : ℝ} (D : ConeBlockFourPointData ν Δ_phi)

/-- **Bilateral Transmuted Crossing & Twist-Gap Hypothesis (`PLAN.md`, Stage 4)**:
At complex rescaled arguments $w_l = \frac{-A + i t_l}{\Delta}$ and
$w_r = \frac{-A + i t_r}{\Delta}$ with $(t_l, t_r) \in [-R, R]^2$, the bilateral Fourier-Laplace
transforms of `D.μ_trans2d Δ` and the exact universal $t$-channel identity measure `D.μ_id2d Δ`
agree up to the non-identity $t$-channel remainder $O\bigl(R^{p_{\text{deg}}}
\Delta^{-2 h_{\text{gap}}}\bigr)$ for **all** $\Delta_\phi > 0$ and $h_{\text{gap}} > 0$. -/
structure HasBilateralCrossingGap (A p_deg : ℝ) : Prop where
  /-- Positivity of the external scaling dimension $\Delta_\phi > 0$. -/
  Δ_phi_pos : 0 < Δ_phi
  /-- Positivity of the $t$-channel non-identity twist gap $h_{\text{gap}} > 0$. -/
  h_gap_pos : 0 < D.h_gap
  /-- Non-negativity of the polynomial frequency growth exponent $p_{\text{deg}} \ge 0$. -/
  p_deg_nonneg : 0 ≤ p_deg
  /-- Exponential integrability of `D.μ_trans2d Δ` at $(-A, -A)$ for all $\Delta \ge 1$. -/
  integrable_trans2d : ∀ {Δ : ℝ}, 1 ≤ Δ →
    Integrable (fun p : ℝ × ℝ => Real.exp (-A * (p.1 + p.2))) (D.μ_trans2d Δ)
  /-- Exponential integrability of `D.μ_id2d Δ` at $(-A, -A)$ for all $\Delta \ge 1$. -/
  integrable_id2d : ∀ {Δ : ℝ}, 1 ≤ Δ →
    Integrable (fun p : ℝ × ℝ => Real.exp (-A * (p.1 + p.2))) (D.μ_id2d Δ)
  /-- Uniform real-Laplace upper bound and pure $O(\Delta^{-2 h_{\text{gap}}})$ complex
  Fourier-Laplace remainder bound on `freqBox R`. -/
  exists_laplace_bound :
    ∃ M > 0, ∃ C_0 > 0, ∀ {Δ : ℝ}, 1 ≤ Δ →
      laplaceTransformReal2d (D.μ_trans2d Δ) (-A) (-A) +
        laplaceTransformReal2d (D.μ_id2d Δ) (-A) (-A) ≤ M ∧
      ∀ {R : ℝ}, 0 < R → ∀ q ∈ freqBox R,
        ‖laplaceTransform2d (D.μ_trans2d Δ)
            ((-A : ℂ) + (q.1 : ℂ) * I) ((-A : ℂ) + (q.2 : ℂ) * I) -
          laplaceTransform2d (D.μ_id2d Δ)
            ((-A : ℂ) + (q.1 : ℂ) * I) ((-A : ℂ) + (q.2 : ℂ) * I)‖ ≤
          C_0 * R ^ p_deg * Δ ^ (- (2 * D.h_gap))

/-!
## Section 2: Theorem 1A — Quantitative Non-Universal Bound Against Exact $t$-Channel Identity
-/

/-- **Theorem 1A — Quantitative Non-Universal 2D Transmuted Bound (`PLAN.md`, Theorem 1A)**:
For **all** $\Delta_\phi > 0$ and **all** $h_{\text{gap}} > 0$, comparing the rescaled 2D
transmuted OPE measure `D.μ_trans2d Δ` against the exact universal $t$-channel identity measure
`D.μ_id2d Δ` yields a power-law error bound $O(\Delta^{-\gamma})$ with exponent
$$\gamma := \frac{2 h_{\text{gap}}}{p_{\text{deg}} + 1} > 0$$
controlled **purely by $2 h_{\text{gap}}$** (with no $\Delta^{-1}$ Stirling barrier and no
$\Delta^{-2\Delta_\phi}$ outer-contour barrier). -/
theorem exists_const_abs_transmuted2d_sub_identity_le
    {A p_deg C_g : ℝ} (hcross : D.HasBilateralCrossingGap A p_deg)
    {ψ : ℝ × ℝ → ℝ} {g : ℝ × ℝ → ℂ}
    (hψ : HasFourierDecay2d (tiltedTest2d A ψ) g C_g) :
    let γ := (2 * D.h_gap) / (p_deg + 1)
    0 < γ ∧ ∃ C_ψ > 0, ∀ {Δ : ℝ}, 1 ≤ Δ →
      |(∫ p : ℝ × ℝ, ψ p ∂(D.μ_trans2d Δ)) -
        (∫ p : ℝ × ℝ, ψ p ∂(D.μ_id2d Δ))| ≤ C_ψ * Δ ^ (-γ) := by
  intro γ
  have hα : 0 < 2 * D.h_gap := by linarith [hcross.h_gap_pos]
  have hp1 : 0 < p_deg + 1 := by linarith [hcross.p_deg_nonneg]
  have hγ_pos : 0 < γ := div_pos hα hp1
  refine ⟨hγ_pos, ?_⟩
  obtain ⟨M, hM, C_0, hC_0, h_lap⟩ := hcross.exists_laplace_bound
  obtain ⟨C_ψ, hC_ψ_pos, h_taub⟩ :=
    exists_const_abs_integral_sub_le_rpow_2d hα hcross.p_deg_nonneg hM hC_0 hψ
  refine ⟨C_ψ, hC_ψ_pos, fun {Δ} hΔ => ?_⟩
  have hΔ_pos : 0 < Δ := lt_of_lt_of_le zero_lt_one hΔ
  have hR_pos : 0 < Δ ^ γ := Real.rpow_pos_of_pos hΔ_pos γ
  exact h_taub hΔ (hcross.integrable_trans2d hΔ) (hcross.integrable_id2d hΔ)
    (h_lap hΔ).1 ((h_lap hΔ).2 hR_pos)

/-- Asymptotic convergence corollary of Theorem 1A: as $\Delta \to \infty$, the difference
between the rescaled 2D transmuted OPE pairing and the exact universal $t$-channel identity
pairing tends to $0$. -/
theorem tendsto_transmuted2d_sub_identity
    {A p_deg C_g : ℝ} (hcross : D.HasBilateralCrossingGap A p_deg)
    {ψ : ℝ × ℝ → ℝ} {g : ℝ × ℝ → ℂ}
    (hψ : HasFourierDecay2d (tiltedTest2d A ψ) g C_g) :
    Tendsto
      (fun Δ : ℝ =>
        (∫ p : ℝ × ℝ, ψ p ∂(D.μ_trans2d Δ)) -
          (∫ p : ℝ × ℝ, ψ p ∂(D.μ_id2d Δ)))
      atTop (𝓝 0) := by
  obtain ⟨hγ_pos, C_ψ, _, h_bd⟩ := D.exists_const_abs_transmuted2d_sub_identity_le hcross hψ
  have h_zero :
      Tendsto (fun Δ : ℝ => C_ψ * Δ ^ (- ((2 * D.h_gap) / (p_deg + 1)))) atTop (𝓝 0) := by
    simpa [mul_zero] using
      (tendsto_rpow_neg_atTop hγ_pos).const_mul C_ψ
  refine squeeze_zero_norm' ?_ h_zero
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with Δ hΔ
  rw [Real.norm_eq_abs]
  exact h_bd hΔ

/-!
## Section 3: Theorem 1B — Quantitative $O(\Delta^{-\gamma})$ Smoothed Primary Bootstrap
-/

/-- The rescaled unweighted $d$-dimensional primary OPE pairing for a two-variable test function
$\chi(u, \xi)$ at scaling dimension cutoff $\Delta$:
$$\Delta^{2\nu - 4\Delta_\phi}
  \int \chi\!\left(\frac{\Delta'}{\Delta},\, \frac{\ell}{\Delta'}\right)
  d\mu_{\text{OPE}}(\Delta', \ell).$$ -/
noncomputable def primaryConePairing (χ : ℝ × ℝ → ℝ) (Δ : ℝ) : ℝ :=
  Δ ^ (2 * ν - 4 * Δ_phi) *
    ∫ p : ℝ × ℕ, χ (p.1 / Δ, (p.2 : ℝ) / p.1) ∂D.μ_OPE

/-- The continuum primary spectral density pairing on $(u, \xi) \in (0, \infty) \times (0, 1)$:
$$\int_0^\infty \int_0^1 \chi(u, \xi) \, \rho^{\text{prim}}_{\nu, \Delta_\phi}(u, \xi)
  \, d\xi \, du.$$ -/
noncomputable def continuumPrimaryPairing (ν Δ_phi : ℝ) (χ : ℝ × ℝ → ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), ∫ ξ in Ioo (0 : ℝ) 1,
    χ (u, ξ) * primaryConeDensity ν Δ_phi u ξ

/-- **Universal $O(\Delta^{-1})$ Branching & Stirling Reduction Hypothesis for a Test Function
$\chi(u, \xi)$ (`PLAN.md`, Stage 4)**:
For a compactly supported smooth test function $\chi$ on $(0, \infty) \times (0, 1)$, there exists
a 2D test function $\psi : \mathbb{R} \times \mathbb{R} \to \mathbb{R}$ (obtained via the inverse
Erdélyi–Kober transform of $\chi$ and division by $\operatorname{transmuteWeight}$) whose tilted
version satisfies `HasFourierDecay2d` and such that:
1. the discrete $d \to 2$ branching error between `D.primaryConePairing χ Δ` and
   `∫ ψ d(D.μ_trans2d Δ)` is $O(\Delta^{-1})$, and
2. the universal Stirling/continuum error between `∫ ψ d(D.μ_id2d Δ)` and
   `continuumPrimaryPairing ν Δ_phi χ` is $O(\Delta^{-1})$. -/
structure HasUniversalBranchingReduction (A : ℝ) (χ : ℝ × ℝ → ℝ) : Prop where
  /-- Existence of the 2D test function $\psi$ and $O(\Delta^{-1})$ universal reduction bounds. -/
  exists_test2d :
    ∃ (ψ : ℝ × ℝ → ℝ) (g : ℝ × ℝ → ℂ) (C_g C_univ : ℝ),
      0 ≤ C_univ ∧
      HasFourierDecay2d (tiltedTest2d A ψ) g C_g ∧
      ∀ {Δ : ℝ}, 1 ≤ Δ →
        |D.primaryConePairing χ Δ - ∫ p : ℝ × ℝ, ψ p ∂(D.μ_trans2d Δ)| ≤ C_univ * Δ ^ (-1 : ℝ) ∧
        |(∫ p : ℝ × ℝ, ψ p ∂(D.μ_id2d Δ)) - continuumPrimaryPairing ν Δ_phi χ| ≤
          C_univ * Δ ^ (-1 : ℝ)

/-- **Theorem 1B — Quantitative $O(\Delta^{-\gamma})$ Smoothed Primary Bootstrap
(`PLAN.md`, Theorem 1B)**:
Combining Theorem 1A (the pure $2 h_{\text{gap}}$ non-universal bound) with the universal
$O(\Delta^{-1})$ Stirling and Erdélyi–Kober branching reduction yields, with
$$\gamma := \min\!\left(\frac{2 h_{\text{gap}}}{p_{\text{deg}} + 1},\; 1\right) > 0,$$
an explicit $O(\Delta^{-\gamma})$ bound between the rescaled unweighted primary OPE pairing and the
continuum primary spectral density pairing for all $\Delta \ge 1$. -/
theorem exists_const_abs_primaryCone_sub_le
    {A p_deg : ℝ} (hcross : D.HasBilateralCrossingGap A p_deg)
    {χ : ℝ × ℝ → ℝ} (huniv : D.HasUniversalBranchingReduction A χ) :
    let γ := min ((2 * D.h_gap) / (p_deg + 1)) 1
    0 < γ ∧ ∃ C_χ > 0, ∀ {Δ : ℝ}, 1 ≤ Δ →
      |D.primaryConePairing χ Δ - continuumPrimaryPairing ν Δ_phi χ| ≤ C_χ * Δ ^ (-γ) := by
  intro γ
  obtain ⟨ψ, g, C_g, C_univ, hC_univ_nonneg, hψ, h_univ_bd⟩ := huniv.exists_test2d
  obtain ⟨hγ0_pos, C_ψ, hC_ψ_pos, h_nonuniv_bd⟩ :=
    D.exists_const_abs_transmuted2d_sub_identity_le hcross hψ
  have hγ_pos : 0 < γ := lt_min hγ0_pos zero_lt_one
  refine ⟨hγ_pos, C_ψ + 2 * C_univ, by positivity, fun {Δ} hΔ => ?_⟩
  have hΔ_pos : 0 < Δ := lt_of_lt_of_le zero_lt_one hΔ
  have h1 := (h_univ_bd hΔ).1
  have h2 := h_nonuniv_bd hΔ
  have h3 := (h_univ_bd hΔ).2
  have hr1 : Δ ^ (- ((2 * D.h_gap) / (p_deg + 1))) ≤ Δ ^ (-γ) := by
    refine Real.rpow_le_rpow_of_exponent_le hΔ ?_
    have : γ ≤ (2 * D.h_gap) / (p_deg + 1) := min_le_left _ _
    linarith
  have hr2 : Δ ^ (-1 : ℝ) ≤ Δ ^ (-γ) := by
    refine Real.rpow_le_rpow_of_exponent_le hΔ ?_
    have : γ ≤ 1 := min_le_right _ _
    linarith
  have h_decomp :
      D.primaryConePairing χ Δ - continuumPrimaryPairing ν Δ_phi χ =
        (D.primaryConePairing χ Δ - ∫ p : ℝ × ℝ, ψ p ∂(D.μ_trans2d Δ)) +
          ((∫ p : ℝ × ℝ, ψ p ∂(D.μ_trans2d Δ)) - ∫ p : ℝ × ℝ, ψ p ∂(D.μ_id2d Δ)) +
          ((∫ p : ℝ × ℝ, ψ p ∂(D.μ_id2d Δ)) - continuumPrimaryPairing ν Δ_phi χ) := by
    ring
  rw [h_decomp]
  have h_tri1 := abs_add_le
    ((D.primaryConePairing χ Δ - ∫ p : ℝ × ℝ, ψ p ∂(D.μ_trans2d Δ)) +
      ((∫ p : ℝ × ℝ, ψ p ∂(D.μ_trans2d Δ)) - ∫ p : ℝ × ℝ, ψ p ∂(D.μ_id2d Δ)))
    ((∫ p : ℝ × ℝ, ψ p ∂(D.μ_id2d Δ)) - continuumPrimaryPairing ν Δ_phi χ)
  have h_tri2 := abs_add_le
    (D.primaryConePairing χ Δ - ∫ p : ℝ × ℝ, ψ p ∂(D.μ_trans2d Δ))
    ((∫ p : ℝ × ℝ, ψ p ∂(D.μ_trans2d Δ)) - ∫ p : ℝ × ℝ, ψ p ∂(D.μ_id2d Δ))
  have h_b1 : C_univ * Δ ^ (-1 : ℝ) ≤ C_univ * Δ ^ (-γ) :=
    mul_le_mul_of_nonneg_left hr2 hC_univ_nonneg
  have h_b2 : C_ψ * Δ ^ (- ((2 * D.h_gap) / (p_deg + 1))) ≤ C_ψ * Δ ^ (-γ) :=
    mul_le_mul_of_nonneg_left hr1 hC_ψ_pos.le
  linarith

/-- **Asymptotic Smoothed Primary Bootstrap (`PLAN.md`, Theorem 1B)**:
as $\Delta \to \infty$, the rescaled unweighted primary OPE pairing converges to the continuum
primary spectral density pairing:
$$\lim_{\Delta \to \infty} \Delta^{2\nu - 4\Delta_\phi}
  \int \chi\!\left(\frac{\Delta'}{\Delta},\, \frac{\ell}{\Delta'}\right)
  d\mu_{\text{OPE}}(\Delta', \ell)
  = \int_0^\infty \int_0^1 \chi(u, \xi) \, \rho^{\text{prim}}_{\nu, \Delta_\phi}(u, \xi)
    \, d\xi \, du.$$ -/
theorem tendsto_primaryConePairing
    {A p_deg : ℝ} (hcross : D.HasBilateralCrossingGap A p_deg)
    {χ : ℝ × ℝ → ℝ} (huniv : D.HasUniversalBranchingReduction A χ) :
    Tendsto (D.primaryConePairing χ) atTop (𝓝 (continuumPrimaryPairing ν Δ_phi χ)) := by
  obtain ⟨hγ_pos, C_χ, _, h_bd⟩ := D.exists_const_abs_primaryCone_sub_le hcross huniv
  rw [← tendsto_sub_nhds_zero_iff]
  have h_zero : Tendsto
      (fun Δ : ℝ => C_χ * Δ ^ (- min ((2 * D.h_gap) / (p_deg + 1)) 1)) atTop (𝓝 0) := by
    simpa [mul_zero] using (tendsto_rpow_neg_atTop hγ_pos).const_mul C_χ
  refine squeeze_zero_norm' ?_ h_zero
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with Δ hΔ
  rw [Real.norm_eq_abs]
  exact h_bd hΔ

/-!
## Section 4: Corollary 2 — Cumulative Spin-Summed Primary Asymptotics
-/

/-- The indicator function of the open unit cylinder $(u, \xi) \in (0, 1) \times (0, 1)$. -/
noncomputable def unitCylinderIndicator (p : ℝ × ℝ) : ℝ :=
  if p.1 ∈ Ioo (0 : ℝ) 1 then (1 : ℝ) else 0

/-- Evaluating `continuumPrimaryPairing` on `unitCylinderIndicator` reproduces the cumulative
primary constant $\mathcal{C}^{\text{prim}}_\nu(\Delta_\phi)$ (`cumulativePrimaryConst ν Δ_phi`). -/
theorem continuumPrimaryPairing_unitCylinderIndicator
    (hν : 0 < ν) (hΔ : ν / 2 + 1 / 4 < Δ_phi) :
    continuumPrimaryPairing ν Δ_phi unitCylinderIndicator =
      cumulativePrimaryConst ν Δ_phi := by
  dsimp [continuumPrimaryPairing, unitCylinderIndicator]
  rw [← integral_primaryConeDensity_cylinder hν hΔ]
  have h_sub : Ioo (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) := Ioo_subset_Ioi_self
  have h_ind :
      (∫ u in Ioi (0 : ℝ),
        ∫ ξ in Ioo (0 : ℝ) 1,
          (if u ∈ Ioo (0 : ℝ) 1 then (1 : ℝ) else 0) * primaryConeDensity ν Δ_phi u ξ) =
      ∫ u in Ioi (0 : ℝ),
        (Ioo (0 : ℝ) 1).indicator
          (fun u => ∫ ξ in Ioo (0 : ℝ) 1, primaryConeDensity ν Δ_phi u ξ) u := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    by_cases hu : u ∈ Ioo (0 : ℝ) 1
    · simp [hu]
    · simp [hu]
  rw [h_ind, setIntegral_indicator measurableSet_Ioo, inter_eq_self_of_subset_right h_sub]

/-- The cumulative unweighted primary OPE spectral weight up to scaling dimension $\Delta$:
$$\operatorname{cumulativePrimaryWeight}(D, \Delta) :=
  \int_{0 < \Delta' \le \Delta} d\mu_{\text{OPE}}(\Delta', \ell).$$ -/
noncomputable def cumulativePrimaryWeight (Δ : ℝ) : ℝ :=
  ∫ p : ℝ × ℕ, (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) (p.1 / Δ) ∂D.μ_OPE

/-- **Corollary 2 — Cumulative Spin-Summed Primary Asymptotics (`PLAN.md`, Corollary 2)**:
For $\nu > 0$ and $\Delta_\phi > \frac{\nu}{2} + \frac{1}{4}$, if the rescaled cumulative primary
weight $\Delta^{2\nu - 4\Delta_\phi} \operatorname{cumulativePrimaryWeight}(D, \Delta)$ can be
sandwiched from below and above by smoothed test functions $\chi_-, \chi_+$ satisfying
`HasUniversalBranchingReduction` whose continuum integrals lie within $\varepsilon$ of the unit
cylinder integral `continuumPrimaryPairing ν Δ_phi unitCylinderIndicator`, then:
$$\lim_{\Delta \to \infty} \Delta^{2\nu - 4\Delta_\phi} \,
  \operatorname{cumulativePrimaryWeight}(D, \Delta)
  = \mathcal{C}^{\text{prim}}_\nu(\Delta_\phi).$$ -/
theorem tendsto_cumulativePrimaryWeight
    {A p_deg : ℝ} (hν : 0 < ν) (hΔ : ν / 2 + 1 / 4 < Δ_phi)
    (hcross : D.HasBilateralCrossingGap A p_deg)
    (h_sand : ∀ ε > 0, ∃ χ_minus χ_plus : ℝ × ℝ → ℝ,
      D.HasUniversalBranchingReduction A χ_minus ∧
      D.HasUniversalBranchingReduction A χ_plus ∧
      (∀ᶠ Δ in atTop,
        D.primaryConePairing χ_minus Δ ≤
          Δ ^ (2 * ν - 4 * Δ_phi) * D.cumulativePrimaryWeight Δ ∧
        Δ ^ (2 * ν - 4 * Δ_phi) * D.cumulativePrimaryWeight Δ ≤
          D.primaryConePairing χ_plus Δ) ∧
      continuumPrimaryPairing ν Δ_phi unitCylinderIndicator - ε ≤
        continuumPrimaryPairing ν Δ_phi χ_minus ∧
      continuumPrimaryPairing ν Δ_phi χ_plus ≤
        continuumPrimaryPairing ν Δ_phi unitCylinderIndicator + ε) :
    Tendsto
      (fun Δ : ℝ => Δ ^ (2 * ν - 4 * Δ_phi) * D.cumulativePrimaryWeight Δ)
      atTop (𝓝 (cumulativePrimaryConst ν Δ_phi)) := by
  rw [← continuumPrimaryPairing_unitCylinderIndicator hν hΔ]
  refine tendsto_of_le_of_ge_approx fun ε hε => ?_
  obtain ⟨χ_minus, χ_plus, hum, hup, h_le, hLm, hLp⟩ := h_sand ε hε
  exact ⟨D.primaryConePairing χ_minus, D.primaryConePairing χ_plus,
    continuumPrimaryPairing ν Δ_phi χ_minus, continuumPrimaryPairing ν Δ_phi χ_plus,
    h_le, D.tendsto_primaryConePairing hcross hum, D.tendsto_primaryConePairing hcross hup,
    hLm, hLp⟩

end ConeBlockFourPointData

end CFT.ConeTauberian
