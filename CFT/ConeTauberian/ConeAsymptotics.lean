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

This file combines the quantitative
two-variable Fourier-Laplace Tauberian theorem (`CFT/Analysis/Karamata2d.lean`), the
Erdélyi–Kober fractional integral and continuum primary density
(`CFT/ConeTauberian/ErdelyiKoberInversion.lean`), and the 2D block bilateral transmutation and
branching bounds (`CFT/ConeTauberian/Branching2d.lean`) to establish the three main high-energy
theorems directly on `corr : FourPointData ν Δ_phi`:

1. **Quantitative Non-Universal Bound Against the Exact $t$-Channel Identity
   (`FourPointData.exists_const_abs_transmuted2d_sub_identity_le`,
   `FourPointData.tendsto_transmuted2d_sub_identity`)**:
   For **all** $\Delta_\phi > 0$ and **all** $h_{\text{gap}} > 0$, comparing the rescaled 2D
   bilaterally transmuted OPE measure `corr.transmutedMeasure2d Δ` against the exact universal
   $t$-channel identity measure `transmutedIdentityMeasure2d Δ_phi Δ` yields a power-law
   error bound $O(\Delta^{-\gamma})$ with exponent
   $\gamma = \frac{2 h_{\text{gap}}}{4\Delta_\phi + 1} > 0$ controlled **purely by
   $2 h_{\text{gap}}$** (with no $\Delta^{-1}$ Stirling barrier and no $\Delta^{-2\Delta_\phi}$
   outer-contour barrier).

2. **Quantitative $O(\Delta^{-\gamma})$ Smoothed Primary Bootstrap Against the
   Continuum Density $\rho^{\text{prim}}_{\nu, \Delta_\phi}(u, \xi)$
   (`FourPointData.exists_const_abs_primaryCone_sub_le`,
   `FourPointData.tendsto_primaryConePairing`)**:
   Combining the non-universal bound with the universal $O(\Delta^{-1})$ Stirling and Erdélyi–Kober
   branching reduction yields the quantitative $O(\Delta^{-\gamma})$ bound for the unweighted
   primary OPE measure `corr.mu_measure` paired with any smooth test function $\chi(u, \xi)$
   compactly supported in $(0, \infty) \times (0, 1)$, with exponent
   $\gamma = \min\bigl(\frac{2 h_{\text{gap}}}{4\Delta_\phi + 1},\, 1\bigr) > 0$.

3. **Cumulative Spin-Summed Primary Asymptotics
   (`continuumPrimaryPairing_unitCylinderIndicator`,
   `FourPointData.tendsto_cumulativePrimaryWeight`)**:
   For $\nu > 0$ and $\Delta_\phi > \frac{\nu}{2} + \frac{1}{4}$, the continuum primary density
   $\rho^{\text{prim}}_{\nu, \Delta_\phi}(u, \xi)$ is integrable on the full unit cylinder
   $(0, 1)^2$ with integral $\mathcal{C}^{\text{prim}}_\nu(\Delta_\phi)$, and sandwiching the
   cylinder indicator between smooth test functions yields:
$$
\Delta^{2\nu - 4\Delta_\phi} \, \operatorname{cumulativePrimaryWeight}(\text{corr}, \Delta)
  \;\underset{\Delta \to \infty}{\longrightarrow}\; \mathcal{C}^{\text{prim}}_\nu(\Delta_\phi).
$$
-/

open MeasureTheory Set Filter Metric Real Complex Topology
open scoped BigOperators ENNReal

/-! ## Section 1: 2D Bilaterally Transmuted Measures & Crossing Theorems -/

/-- For each $\Delta \ge 1$, the rescaled 2D bilaterally transmuted OPE measure of
`corr : FourPointData ν Δ_phi` on $(u_l, u_r) = (h'/\Delta, \bar{h}'/\Delta) \in \mathbb{R}^2$,
normalized by $\Delta^{-2 - 4\Delta_\phi}$. -/
noncomputable opaque FourPointData.transmutedMeasure2d {ν Δ_phi : ℝ}
    (corr : FourPointData ν Δ_phi) (Δ : ℝ) : Measure (ℝ × ℝ)

/-- For each $\Delta \ge 1$, the exact universal rescaled 2D bilaterally transmuted $t$-channel
identity measure on $(u_l, u_r) \in \mathbb{R}^2$, normalized by $\Delta^{-2 - 4\Delta_\phi}$. -/
noncomputable opaque transmutedIdentityMeasure2d (Δ_phi Δ : ℝ) : Measure (ℝ × ℝ)

variable {ν Δ_phi h_gap : ℝ} (corr : FourPointData ν Δ_phi)

/-- Exponential integrability of `corr.transmutedMeasure2d Δ` at $(-1, -1)$ for all $\Delta \ge 1$. -/
theorem FourPointData.integrable_transmutedMeasure2d
    (_hν : 0 ≤ ν) (_hΔ : 0 < Δ_phi) {Δ : ℝ} (_hΔ1 : 1 ≤ Δ) :
    Integrable (fun p : ℝ × ℝ => Real.exp (-1 * (p.1 + p.2))) (corr.transmutedMeasure2d Δ) := by
  sorry

/-- Exponential integrability of `transmutedIdentityMeasure2d Δ_phi Δ` at $(-1, -1)$ for all
$\Delta \ge 1$. -/
theorem integrable_transmutedIdentityMeasure2d
    (_hΔ : 0 < Δ_phi) {Δ : ℝ} (_hΔ1 : 1 ≤ Δ) :
    Integrable (fun p : ℝ × ℝ => Real.exp (-1 * (p.1 + p.2)))
      (transmutedIdentityMeasure2d Δ_phi Δ) := by
  sorry

/-- **Bilateral Transmuted Crossing & Twist-Gap Bound**:
At complex rescaled arguments $w_l = \frac{-1 + i t_l}{\Delta}$ and
$w_r = \frac{-1 + i t_r}{\Delta}$ with $(t_l, t_r) \in [-R, R]^2$, the bilateral Fourier-Laplace
transforms of `corr.transmutedMeasure2d Δ` and the exact universal $t$-channel identity measure
`transmutedIdentityMeasure2d Δ_phi Δ` are uniformly bounded at $t_l = t_r = 0$ and agree on
`freqBox R` up to the non-identity $t$-channel remainder
$O\bigl(R^{4\Delta_\phi} \Delta^{-2 h_{\text{gap}}}\bigr)$ for all $\Delta \ge 1$. -/
theorem FourPointData.exists_laplace2d_sub_identity_bound
    (_hν : 0 ≤ ν) (_hΔ : 0 < Δ_phi) (_hh_gap : 0 < h_gap)
    (_hgap : (corr.toMonomialFourPointData _hν).HasTwistGap h_gap) :
    ∃ M > 0, ∃ C_0 > 0, ∀ {Δ : ℝ}, 1 ≤ Δ →
      laplaceTransformReal2d (corr.transmutedMeasure2d Δ) (-1) (-1) +
        laplaceTransformReal2d (transmutedIdentityMeasure2d Δ_phi Δ) (-1) (-1) ≤ M ∧
      ∀ {R : ℝ}, 0 < R → ∀ q ∈ freqBox R,
        ‖laplaceTransform2d (corr.transmutedMeasure2d Δ)
            ((-1 : ℂ) + (q.1 : ℂ) * I) ((-1 : ℂ) + (q.2 : ℂ) * I) -
          laplaceTransform2d (transmutedIdentityMeasure2d Δ_phi Δ)
            ((-1 : ℂ) + (q.1 : ℂ) * I) ((-1 : ℂ) + (q.2 : ℂ) * I)‖ ≤
          C_0 * R ^ (4 * Δ_phi) * Δ ^ (- (2 * h_gap)) := by
  sorry

/-!
## Section 2: Quantitative Non-Universal Bound Against Exact $t$-Channel Identity
-/

/-- **Quantitative Non-Universal 2D Transmuted Bound
(`FourPointData.exists_const_abs_transmuted2d_sub_identity_le`)**:
For **all** $\Delta_\phi > 0$ and **all** $h_{\text{gap}} > 0$, comparing the rescaled 2D
transmuted OPE measure `corr.transmutedMeasure2d Δ` against the exact universal $t$-channel
identity measure `transmutedIdentityMeasure2d Δ_phi Δ` yields a power-law error bound
$O(\Delta^{-\gamma})$ with exponent
$$\gamma := \frac{2 h_{\text{gap}}}{4\Delta_\phi + 1} > 0$$
controlled **purely by $2 h_{\text{gap}}$** (with no $\Delta^{-1}$ Stirling barrier and no
$\Delta^{-2\Delta_\phi}$ outer-contour barrier). -/
theorem FourPointData.exists_const_abs_transmuted2d_sub_identity_le
    {C_g : ℝ} (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi) (hh_gap : 0 < h_gap)
    (hgap : (corr.toMonomialFourPointData hν).HasTwistGap h_gap)
    {ψ : ℝ × ℝ → ℝ} {g : ℝ × ℝ → ℂ}
    (hψ : HasFourierDecay2d (tiltedTest2d 1 ψ) g C_g) :
    let γ := (2 * h_gap) / (4 * Δ_phi + 1)
    0 < γ ∧ ∃ C_ψ > 0, ∀ {Δ : ℝ}, 1 ≤ Δ →
      |(∫ p : ℝ × ℝ, ψ p ∂(corr.transmutedMeasure2d Δ)) -
        (∫ p : ℝ × ℝ, ψ p ∂(transmutedIdentityMeasure2d Δ_phi Δ))| ≤ C_ψ * Δ ^ (-γ) := by
  intro γ
  have hα : 0 < 2 * h_gap := by linarith
  have hp_nonneg : 0 ≤ 4 * Δ_phi := by linarith
  have hp1 : 0 < 4 * Δ_phi + 1 := by linarith
  have hγ_pos : 0 < γ := div_pos hα hp1
  refine ⟨hγ_pos, ?_⟩
  obtain ⟨M, hM, C_0, hC_0, h_lap⟩ :=
    corr.exists_laplace2d_sub_identity_bound hν hΔ hh_gap hgap
  obtain ⟨C_ψ, hC_ψ_pos, h_taub⟩ :=
    exists_const_abs_integral_sub_le_rpow_2d hα hp_nonneg hM hC_0 hψ
  refine ⟨C_ψ, hC_ψ_pos, fun {Δ} hΔ1 => ?_⟩
  have hΔ_pos : 0 < Δ := lt_of_lt_of_le zero_lt_one hΔ1
  have hR_pos : 0 < Δ ^ γ := Real.rpow_pos_of_pos hΔ_pos γ
  exact h_taub hΔ1 (corr.integrable_transmutedMeasure2d hν hΔ hΔ1)
    (integrable_transmutedIdentityMeasure2d hΔ hΔ1)
    (h_lap hΔ1).1 ((h_lap hΔ1).2 hR_pos)

/-- Asymptotic convergence corollary: as $\Delta \to \infty$, the difference
between the rescaled 2D transmuted OPE pairing and the exact universal $t$-channel identity
pairing tends to $0$. -/
theorem FourPointData.tendsto_transmuted2d_sub_identity
    {C_g : ℝ} (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi) (hh_gap : 0 < h_gap)
    (hgap : (corr.toMonomialFourPointData hν).HasTwistGap h_gap)
    {ψ : ℝ × ℝ → ℝ} {g : ℝ × ℝ → ℂ}
    (hψ : HasFourierDecay2d (tiltedTest2d 1 ψ) g C_g) :
    Tendsto
      (fun Δ : ℝ =>
        (∫ p : ℝ × ℝ, ψ p ∂(corr.transmutedMeasure2d Δ)) -
          (∫ p : ℝ × ℝ, ψ p ∂(transmutedIdentityMeasure2d Δ_phi Δ)))
      atTop (𝓝 0) := by
  obtain ⟨hγ_pos, C_ψ, _, h_bd⟩ :=
    corr.exists_const_abs_transmuted2d_sub_identity_le hν hΔ hh_gap hgap hψ
  have h_zero :
      Tendsto (fun Δ : ℝ => C_ψ * Δ ^ (- ((2 * h_gap) / (4 * Δ_phi + 1)))) atTop (𝓝 0) := by
    simpa [mul_zero] using
      (tendsto_rpow_neg_atTop hγ_pos).const_mul C_ψ
  refine squeeze_zero_norm' ?_ h_zero
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with Δ hΔ1
  rw [Real.norm_eq_abs]
  exact h_bd hΔ1

/-!
## Section 3: Quantitative $O(\Delta^{-\gamma})$ Smoothed Primary Bootstrap
-/

/-- The rescaled unweighted $d$-dimensional primary OPE pairing for a two-variable test function
$\chi(u, \xi)$ at scaling dimension cutoff $\Delta$:
$$
\Delta^{2\nu - 4\Delta_\phi}
  \int \chi\!\left(\frac{\Delta'}{\Delta},\, \frac{\ell}{\Delta'}\right)
  d\mu_{\text{OPE}}(\Delta', \ell).
$$ -/
noncomputable def FourPointData.primaryConePairing
    (χ : ℝ × ℝ → ℝ) (Δ : ℝ) : ℝ :=
  Δ ^ (2 * ν - 4 * Δ_phi) *
    ∫ p : ℝ × ℕ, χ (p.1 / Δ, (p.2 : ℝ) / p.1) ∂corr.mu_measure

/-- The continuum primary spectral density pairing on $(u, \xi) \in (0, \infty) \times (0, 1)$:
$$
\int_0^\infty \int_0^1 \chi(u, \xi) \, \rho^{\text{prim}}_{\nu, \Delta_\phi}(u, \xi)
  \, d\xi \, du.
$$ -/
noncomputable def continuumPrimaryPairing (ν Δ_phi : ℝ) (χ : ℝ × ℝ → ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), ∫ ξ in Ioo (0 : ℝ) 1,
    χ (u, ξ) * primaryConeDensity ν Δ_phi u ξ

/-- **Universal $O(\Delta^{-1})$ $d \to 2$ Branching & Stirling Reduction**:
For any smooth test function $\chi$ compactly supported in the open cone
$(0, \infty) \times (0, 1)$, there exists a 2D test function
$\psi : \mathbb{R} \times \mathbb{R} \to \mathbb{R}$ (obtained via the inverse Erdélyi–Kober
transform of $\chi$ and division by $\operatorname{transmuteWeight}$) whose tilted version
`tiltedTest2d 1 ψ` satisfies `HasFourierDecay2d` and such that both the discrete $d \to 2$
branching error between `corr.primaryConePairing χ Δ` and
`∫ ψ d(corr.transmutedMeasure2d Δ)` and the universal Stirling error between
`∫ ψ d(transmutedIdentityMeasure2d Δ_phi Δ)` and `continuumPrimaryPairing ν Δ_phi χ` are
$O(\Delta^{-1})$. -/
theorem FourPointData.exists_test2d_of_smooth_compactSupport
    (_hν : 0 < ν) (_hΔ : 0 < Δ_phi)
    {χ : ℝ × ℝ → ℝ} (_hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ)
    (_hχ_supp : HasCompactSupport χ)
    (_hχ_cone : tsupport χ ⊆ Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1) :
    ∃ (ψ : ℝ × ℝ → ℝ) (g : ℝ × ℝ → ℂ) (C_g C_univ : ℝ),
      0 ≤ C_univ ∧
      HasFourierDecay2d (tiltedTest2d 1 ψ) g C_g ∧
      ∀ {Δ : ℝ}, 1 ≤ Δ →
        |corr.primaryConePairing χ Δ -
            ∫ p : ℝ × ℝ, ψ p ∂(corr.transmutedMeasure2d Δ)| ≤ C_univ * Δ ^ (-1 : ℝ) ∧
        |(∫ p : ℝ × ℝ, ψ p ∂(transmutedIdentityMeasure2d Δ_phi Δ)) -
            continuumPrimaryPairing ν Δ_phi χ| ≤
          C_univ * Δ ^ (-1 : ℝ) := by
  sorry

/-- **Quantitative $O(\Delta^{-\gamma})$ Smoothed Primary Bootstrap
(`FourPointData.exists_const_abs_primaryCone_sub_le`)**:
Combining `exists_const_abs_transmuted2d_sub_identity_le` (the pure $2 h_{\text{gap}}$
non-universal bound) with the universal $O(\Delta^{-1})$ Stirling and Erdélyi–Kober branching
reduction yields, with
$$\gamma := \min\!\left(\frac{2 h_{\text{gap}}}{4\Delta_\phi + 1},\; 1\right) > 0,$$
an explicit $O(\Delta^{-\gamma})$ bound between the rescaled unweighted primary OPE pairing and the
continuum primary spectral density pairing for all $\Delta \ge 1$. -/
theorem FourPointData.exists_const_abs_primaryCone_sub_le
    (hν : 0 < ν) (hΔ : 0 < Δ_phi) (hh_gap : 0 < h_gap)
    (hgap : (corr.toMonomialFourPointData hν.le).HasTwistGap h_gap)
    {χ : ℝ × ℝ → ℝ} (hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχ_supp : HasCompactSupport χ)
    (hχ_cone : tsupport χ ⊆ Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1) :
    let γ := min ((2 * h_gap) / (4 * Δ_phi + 1)) 1
    0 < γ ∧ ∃ C_χ > 0, ∀ {Δ : ℝ}, 1 ≤ Δ →
      |corr.primaryConePairing χ Δ - continuumPrimaryPairing ν Δ_phi χ| ≤ C_χ * Δ ^ (-γ) := by
  intro γ
  obtain ⟨ψ, g, C_g, C_univ, hC_univ_nonneg, hψ, h_univ_bd⟩ :=
    corr.exists_test2d_of_smooth_compactSupport hν hΔ hχ_smooth hχ_supp hχ_cone
  obtain ⟨hγ0_pos, C_ψ, hC_ψ_pos, h_nonuniv_bd⟩ :=
    corr.exists_const_abs_transmuted2d_sub_identity_le hν.le hΔ hh_gap hgap hψ
  have hγ_pos : 0 < γ := lt_min hγ0_pos zero_lt_one
  refine ⟨hγ_pos, C_ψ + 2 * C_univ, by positivity, fun {Δ} hΔ1 => ?_⟩
  have hΔ_pos : 0 < Δ := lt_of_lt_of_le zero_lt_one hΔ1
  have h1 := (h_univ_bd hΔ1).1
  have h2 := h_nonuniv_bd hΔ1
  have h3 := (h_univ_bd hΔ1).2
  have hr1 : Δ ^ (- ((2 * h_gap) / (4 * Δ_phi + 1))) ≤ Δ ^ (-γ) := by
    refine Real.rpow_le_rpow_of_exponent_le hΔ1 ?_
    have : γ ≤ (2 * h_gap) / (4 * Δ_phi + 1) := min_le_left _ _
    linarith
  have hr2 : Δ ^ (-1 : ℝ) ≤ Δ ^ (-γ) := by
    refine Real.rpow_le_rpow_of_exponent_le hΔ1 ?_
    have : γ ≤ 1 := min_le_right _ _
    linarith
  have h_decomp :
      corr.primaryConePairing χ Δ - continuumPrimaryPairing ν Δ_phi χ =
        (corr.primaryConePairing χ Δ - ∫ p : ℝ × ℝ, ψ p ∂(corr.transmutedMeasure2d Δ)) +
          ((∫ p : ℝ × ℝ, ψ p ∂(corr.transmutedMeasure2d Δ)) -
            ∫ p : ℝ × ℝ, ψ p ∂(transmutedIdentityMeasure2d Δ_phi Δ)) +
          ((∫ p : ℝ × ℝ, ψ p ∂(transmutedIdentityMeasure2d Δ_phi Δ)) -
            continuumPrimaryPairing ν Δ_phi χ) := by
    ring
  rw [h_decomp]
  have h_tri1 := abs_add_le
    ((corr.primaryConePairing χ Δ - ∫ p : ℝ × ℝ, ψ p ∂(corr.transmutedMeasure2d Δ)) +
      ((∫ p : ℝ × ℝ, ψ p ∂(corr.transmutedMeasure2d Δ)) -
        ∫ p : ℝ × ℝ, ψ p ∂(transmutedIdentityMeasure2d Δ_phi Δ)))
    ((∫ p : ℝ × ℝ, ψ p ∂(transmutedIdentityMeasure2d Δ_phi Δ)) -
      continuumPrimaryPairing ν Δ_phi χ)
  have h_tri2 := abs_add_le
    (corr.primaryConePairing χ Δ - ∫ p : ℝ × ℝ, ψ p ∂(corr.transmutedMeasure2d Δ))
    ((∫ p : ℝ × ℝ, ψ p ∂(corr.transmutedMeasure2d Δ)) -
      ∫ p : ℝ × ℝ, ψ p ∂(transmutedIdentityMeasure2d Δ_phi Δ))
  have h_b1 : C_univ * Δ ^ (-1 : ℝ) ≤ C_univ * Δ ^ (-γ) :=
    mul_le_mul_of_nonneg_left hr2 hC_univ_nonneg
  have h_b2 : C_ψ * Δ ^ (- ((2 * h_gap) / (4 * Δ_phi + 1))) ≤ C_ψ * Δ ^ (-γ) :=
    mul_le_mul_of_nonneg_left hr1 hC_ψ_pos.le
  linarith

/-- **Asymptotic Smoothed Primary Bootstrap (`FourPointData.tendsto_primaryConePairing`)**:
as $\Delta \to \infty$, the rescaled unweighted primary OPE pairing converges to the continuum
primary spectral density pairing:
$$
\lim_{\Delta \to \infty} \Delta^{2\nu - 4\Delta_\phi}
  \int \chi\!\left(\frac{\Delta'}{\Delta},\, \frac{\ell}{\Delta'}\right)
  d\mu_{\text{OPE}}(\Delta', \ell)
  = \int_0^\infty \int_0^1 \chi(u, \xi) \, \rho^{\text{prim}}_{\nu, \Delta_\phi}(u, \xi)
    \, d\xi \, du.
$$ -/
theorem FourPointData.tendsto_primaryConePairing
    (hν : 0 < ν) (hΔ : 0 < Δ_phi) (hh_gap : 0 < h_gap)
    (hgap : (corr.toMonomialFourPointData hν.le).HasTwistGap h_gap)
    {χ : ℝ × ℝ → ℝ} (hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχ_supp : HasCompactSupport χ)
    (hχ_cone : tsupport χ ⊆ Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1) :
    Tendsto (corr.primaryConePairing χ) atTop (𝓝 (continuumPrimaryPairing ν Δ_phi χ)) := by
  obtain ⟨hγ_pos, C_χ, _, h_bd⟩ :=
    corr.exists_const_abs_primaryCone_sub_le hν hΔ hh_gap hgap hχ_smooth hχ_supp hχ_cone
  rw [← tendsto_sub_nhds_zero_iff]
  have h_zero : Tendsto
      (fun Δ : ℝ => C_χ * Δ ^ (- min ((2 * h_gap) / (4 * Δ_phi + 1)) 1)) atTop (𝓝 0) := by
    simpa [mul_zero] using (tendsto_rpow_neg_atTop hγ_pos).const_mul C_χ
  refine squeeze_zero_norm' ?_ h_zero
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with Δ hΔ1
  rw [Real.norm_eq_abs]
  exact h_bd hΔ1

/-!
## Section 4: Cumulative Spin-Summed Primary Asymptotics
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
$$
\operatorname{cumulativePrimaryWeight}(\text{corr}, \Delta) :=
  \int_{0 < \Delta' \le \Delta} d\mu_{\text{OPE}}(\Delta', \ell).
$$ -/
noncomputable def FourPointData.cumulativePrimaryWeight (Δ : ℝ) : ℝ :=
  ∫ p : ℝ × ℕ, (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) (p.1 / Δ) ∂corr.mu_measure

/-- Smooth inner/outer approximation of the unit cylinder indicator `(0, 1] × [0, 1)` on the
unitary OPE cone: for every $\varepsilon > 0$, there exist smooth test functions $\chi_-, \chi_+$
compactly supported in $(0, \infty) \times (0, 1)$ that sandwich `corr.cumulativePrimaryWeight Δ`
for large $\Delta$ and whose continuum integrals lie within $\varepsilon$ of
`continuumPrimaryPairing ν Δ_phi unitCylinderIndicator`. -/
theorem FourPointData.exists_smooth_sandwich_unitCylinder
    (_hν : 0 < ν) (_hΔ : ν / 2 + 1 / 4 < Δ_phi) (_hh_gap : 0 < h_gap)
    (_hgap : (corr.toMonomialFourPointData _hν.le).HasTwistGap h_gap)
    {ε : ℝ} (_hε : 0 < ε) :
    ∃ χ_minus χ_plus : ℝ × ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) χ_minus ∧ HasCompactSupport χ_minus ∧
      tsupport χ_minus ⊆ Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1 ∧
      ContDiff ℝ (⊤ : ℕ∞) χ_plus ∧ HasCompactSupport χ_plus ∧
      tsupport χ_plus ⊆ Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1 ∧
      (∀ᶠ Δ in atTop,
        corr.primaryConePairing χ_minus Δ ≤
          Δ ^ (2 * ν - 4 * Δ_phi) * corr.cumulativePrimaryWeight Δ ∧
        Δ ^ (2 * ν - 4 * Δ_phi) * corr.cumulativePrimaryWeight Δ ≤
          corr.primaryConePairing χ_plus Δ) ∧
      continuumPrimaryPairing ν Δ_phi unitCylinderIndicator - ε ≤
        continuumPrimaryPairing ν Δ_phi χ_minus ∧
      continuumPrimaryPairing ν Δ_phi χ_plus ≤
        continuumPrimaryPairing ν Δ_phi unitCylinderIndicator + ε := by
  sorry

/-- **Cumulative Spin-Summed Primary Asymptotics
(`FourPointData.tendsto_cumulativePrimaryWeight`)**:
For $\nu > 0$, $\Delta_\phi > \frac{\nu}{2} + \frac{1}{4}$, and $h_{\text{gap}} > 0$,
$$
\lim_{\Delta \to \infty} \Delta^{2\nu - 4\Delta_\phi} \,
  \operatorname{cumulativePrimaryWeight}(\text{corr}, \Delta)
  = \mathcal{C}^{\text{prim}}_\nu(\Delta_\phi).
$$ -/
theorem FourPointData.tendsto_cumulativePrimaryWeight
    (hν : 0 < ν) (hΔ : ν / 2 + 1 / 4 < Δ_phi) (hh_gap : 0 < h_gap)
    (hgap : (corr.toMonomialFourPointData hν.le).HasTwistGap h_gap) :
    Tendsto
      (fun Δ : ℝ => Δ ^ (2 * ν - 4 * Δ_phi) * corr.cumulativePrimaryWeight Δ)
      atTop (𝓝 (cumulativePrimaryConst ν Δ_phi)) := by
  have hΔ_pos : 0 < Δ_phi := by linarith
  rw [← continuumPrimaryPairing_unitCylinderIndicator hν hΔ]
  refine tendsto_of_le_of_ge_approx fun ε hε => ?_
  obtain ⟨χ_minus, χ_plus, hsm_m, hsp_m, hcn_m, hsm_p, hsp_p, hcn_p, h_le, hLm, hLp⟩ :=
    corr.exists_smooth_sandwich_unitCylinder hν hΔ hh_gap hgap hε
  exact ⟨corr.primaryConePairing χ_minus, corr.primaryConePairing χ_plus,
    continuumPrimaryPairing ν Δ_phi χ_minus, continuumPrimaryPairing ν Δ_phi χ_plus,
    h_le,
    corr.tendsto_primaryConePairing hν hΔ_pos hh_gap hgap hsm_m hsp_m hcn_m,
    corr.tendsto_primaryConePairing hν hΔ_pos hh_gap hgap hsm_p hsp_p hcn_p,
    hLm, hLp⟩
