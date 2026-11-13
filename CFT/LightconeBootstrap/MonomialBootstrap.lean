/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Balt van Rees
-/
import CFT.LightconeBootstrap.Monomial.ReferencePairing

/-!
# Stage I: Quantitative Monomial Lightcone Bootstrap

This file is the first of the three top-level milestones in `CFT.LightconeBootstrap`
(`MonomialBootstrap` $\to$ `LightconeBlockBootstrap` $\to$ `PrimaryBootstrap`). It serves two
purposes:
1. **Section 1 (`MonomialFourPointData.exists_const_abs_rescaled_pairSpin_sub_le`)**: Establishes
   the **Master Tauberian Reduction** for any abstract radial monomial decomposition
   (`MonomialFourPointData`), converting uniform real-axis Laplace bounds at spin $2k$ into
   quantitative $O((2k)^{-\gamma})$ asymptotics for $C_c^2$ test-function pairings in the twist
   variable. This theorem is the shared Tauberian engine used both here (Stage I) and after 1D
   collinear block transmutation in `CFT.LightconeBootstrap.LightconeBlockBootstrap` (Stage II).
2. **Section 2 (`exists_const_abs_pairSpin_sub_identity_le`,
   `exists_const_abs_pairSpin_sub_universal_le`)**: Specializes Section 1 to the untransmuted
   radial monomial expansion of a reflection-positive CFT four-point function for
   $\Delta_\phi > 1/2$.

---

## Mathematical Setup and Dictionary of Lean Types

Consider a unitary / reflection-positive four-point function of four identical scalar primary
operators $\phi$ of scaling dimension $\Delta_\phi > 0$ in spacetime dimension
$d = 2\nu + 2 \ge 2$ ($\nu \ge 0$), packaged in Lean as `corr : FourPointData ν Δ_phi`.

### 1. Radial coordinates and the monomial expansion (`MonomialFourPointData`)
In radial coordinates $\rho(z_l) = e^{w_l}$ and $\rho(z_r) = e^{w_r}$, the $s$-channel four-point
function `corr.correlator_pdisk wl wr` is holomorphic on the product of left half-planes
$$\operatorname{UcPdisk} = \lbrace (w_l, w_r) \in \mathbb{C}^2 \mid
  \operatorname{Re} w_l < 0,\thinspace \operatorname{Re} w_r < 0 \rbrace.$$
Expanding each $s$-channel conformal block into positive radial and Gegenbauer monomials
$e^{h w_l + (h + J) w_r}$ — where $h = (\Delta - J)/2 \ge 0$ is the **radial twist** and
$J \in 2\mathbb{Z}_{\ge 0}$ is the **even radial spin** — represents the correlator as an instance
of `MonomialFourPointData` (constructed in `CFT.LightconeBootstrap.Monomial.Decomp` as
`corr.toMonomialFourPointData hν`):
$$\mathcal{G}(w_l, w_r) = \sum_{J \in 2\mathbb{Z}} e^{J w_r}
  \int_{[0, \infty)} e^{h(w_l + w_r)} \thinspace d\mu_J(h).$$
For any `M : MonomialFourPointData`, the key operations are:
- `M.mu J : Measure ℝ`: the non-negative spectral measure $\mu_J$ supported on $[0, \infty)$
  (and vanishing for odd $J$),
- `M.eval wl wr : ℂ`: the complex correlator value $\mathcal{G}(w_l, w_r)$ on
  $\operatorname{UcPdisk}$,
- `M.laplaceSpinReal J σ : ℝ`: the real-axis twist Laplace transform at spin $J$,
  $$\mathcal{L}_J(\sigma) =
    \int_{[0, \infty)} e^{h\sigma} \thinspace d\mu_J(h) \quad (\sigma < 0),$$
- `M.pairSpin J φ : ℝ`: the spectral pairing against a compactly supported test function
  $\varphi : \mathbb{R} \to \mathbb{R}$ of the twist $h$,
  $$\langle \mu_J, \varphi \rangle = \int_{[0, \infty)} \varphi(h) \thinspace d\mu_J(h).$$

### 2. Crossing symmetry and the $t$-channel identity reference
Under crossing $z \leftrightarrow 1 - z$, the $s$-channel correlator is controlled in the lightcone
regime $\operatorname{Re} w_r \to 0^-$ (with $w_l + w_r = \sigma < 0$ held fixed) by the $t$-channel
identity exchange, which factorizes into left- and right-moving binomial series:
$$\operatorname{crossFactor}(\Delta_\phi, w_l)\thinspace
  \operatorname{crossFactor}(\Delta_\phi, w_r)
  = 2 \cdot 4^{2\Delta_\phi} \thinspace e^{\Delta_\phi(w_l + w_r)}
    (1 - e^{w_l})^{-2\Delta_\phi} (1 - e^{w_r})^{-2\Delta_\phi},$$
where $(1 - e^w)^{-2\Delta_\phi} = \sum_{m=0}^\infty \frac{(2\Delta_\phi)_m}{m!} e^{m w}$ and
$\frac{(2\Delta_\phi)_m}{m!}$ is `pochhammerCoeff (2 * Δ_phi) m`.
Assuming a $t$-channel twist gap $h \ge h_{\text{gap}} > 0$ above the vacuum
(`corr.HasTwistGap h_gap` or `M.HasTwistGap h_gap`), all non-vacuum $t$-channel exchanges are
suppressed near $w_r = 0$ by $O\bigl(|1 - e^{w_r}|^{2 h_{\text{gap}}}\bigr)$
(`CFT.LightconeBootstrap.Monomial.TwistGap`).

Projecting onto even spin $J = 2k$ via the Fourier contour $w_r = -\frac{1}{2k} + i\theta$
($\theta \in [-\pi, \pi]$) and rescaling by $(2k)^{1 - 2\Delta_\phi}$ compares `M.pairSpin (2k) φ`
against two natural discrete reference pairings supported on the double-twist lattice
$h_n = \Delta_\phi + n$ ($n \in \mathbb{N}$), defined in
`CFT.LightconeBootstrap.Monomial.ReferencePairing`:

1. **Exact finite-spin $t$-channel identity pairing (`identityMonomialPairing`)**:
   $$\operatorname{identityMonomialPairing}(\Delta_\phi, 2k, \varphi)
     = 2 \cdot 4^{2\Delta_\phi} \sum_{n=0}^{\infty}
       \frac{(2\Delta_\phi)_n}{n!} \frac{(2\Delta_\phi)_{n+2k}}{(n+2k)!} \thinspace
       \varphi(\Delta_\phi + n).$$
   Because this reference retains the exact finite-$k$ binomial coefficient
   $\frac{(2\Delta_\phi)_{n+2k}}{(n+2k)!}$ from $(1 - e^{w_r})^{-2\Delta_\phi}$ rather than its
   $k \to \infty$ Stirling limit, comparing against
   $(2k)^{1 - 2\Delta_\phi} \operatorname{identityMonomialPairing}(\Delta_\phi, 2k, \varphi)$ incurs
   **no $O(k^{-1})$ Stirling approximation error**. The only error sources are the $t$-channel
   non-vacuum remainder $O\bigl((2k)^{-2 h_{\text{gap}}}\bigr)$ near $\theta = 0$ and the
   outer-arc contour tail $O\bigl((2k)^{1 - 2\Delta_\phi}\bigr)$ on $|\theta| \in [\pi/2, \pi]$
   where $|1 - e^{w_r}|$ is bounded away from zero, yielding the exponent range
   $$0 < \gamma < \min(2 h_{\text{gap}},\thinspace 2\Delta_\phi - 1).$$
2. **Universal large-spin Gamma pairing (`universalMonomialPairing`)**:
   $$\operatorname{universalMonomialPairing}(\Delta_\phi, \varphi)
     = \frac{2 \cdot 4^{2\Delta_\phi}}{\Gamma(2\Delta_\phi)} \sum_{n=0}^{\infty}
       \frac{(2\Delta_\phi)_n}{n!} \thinspace \varphi(\Delta_\phi + n).$$
   Replacing $\frac{(2\Delta_\phi)_{n+2k}}{(n+2k)!}$ by
   $\frac{(2k)^{2\Delta_\phi - 1}}{\Gamma(2\Delta_\phi)}$ introduces a kinematic $O(k^{-1})$
   Stirling error, giving the exponent range
   $$0 < \gamma < \min\bigl(2 h_{\text{gap}},\thinspace \min(1,\thinspace 2\Delta_\phi - 1)\bigr).$$

> **Why Stage II is needed for $\Delta_\phi \le 1/2$:** In the untransmuted monomial expansion
> above, the outer arc $|\theta| \in [\pi/2, \pi]$ is only suppressed after multiplying by
> $(2k)^{1 - 2\Delta_\phi}$ when $2\Delta_\phi - 1 > 0$, i.e. $\Delta_\phi > 1/2$. In
> `CFT.LightconeBootstrap.LightconeBlockBootstrap`, applying a 1D fractional integral transmutation
> operator in $w_r$ replaces the right-moving monomials by collinear blocks and boosts the
> $t$-channel identity singularity from $(1 - e^{w_r})^{-2\Delta_\phi}$ to
> $(1 - e^{w_r})^{-(2\Delta_\phi + 1)}$, replacing $2\Delta_\phi - 1$ by $2\Delta_\phi$ and removing
> the $\Delta_\phi > 1/2$ restriction.
-/

open MeasureTheory Set Filter Metric Real Complex Topology
open scoped ENNReal

namespace MonomialFourPointData

variable (M : MonomialFourPointData)

/-!
## 1. Master Tauberian Reduction for `MonomialFourPointData`

Given any `M : MonomialFourPointData` and a family of discrete reference measures $\nu_k$ supported
on $\mathbb{Z}$ (representing the lattice of double-twist shifts
$u = h - \Delta_\phi \in \mathbb{Z}$), `exists_const_abs_rescaled_pairSpin_sub_le` reduces
quantitative $O((2k)^{-\gamma})$ bounds on the rescaled spectral pairing
$(2k)^s \langle \mu_{2k}, \varphi \rangle$ to uniform $O((2k)^{-\alpha})$ agreement of the real-axis
Laplace transforms on the compact interval $\sigma \in [1 - 2A, -1] \subset (-\infty, 0)$.

Internally, this theorem shifts the twist variable by $\Delta_\phi$ (`rescaledShiftedMeasure` and
`shiftedTest` from `CFT.LightconeBootstrap.Monomial.ReferencePairing`) and invokes the complex
analytic Laplace Tauberian theorem `exists_const_abs_integral_sub_le_rpow` from
`CFT.Analysis.LaplaceTauberian` (which propagates real-interval Laplace bounds to vertical lines via
the two-constants theorem on a half-disk and inverts the Laplace transform against $C_c^2$ test
functions).
-/

/-- **Master Tauberian Reduction for Rescaled Spin-$2k$ Monomial Pairings**:
Let `M : MonomialFourPointData` be a radial monomial decomposition and let $s \in \mathbb{R}$ be a
spin-rescaling exponent ($s = 1 - 2\Delta_\phi$ in Stage I; $s = -2\Delta_\phi$ after 1D
transmutation in Stage II). Suppose that on the compact real Laplace interval
$\sigma \in [1 - 2A, -1]$ ($A > 1$), the rescaled spin-$2k$ Laplace transform
$(2k)^s \mathcal{L}_{2k}(\sigma)$ and a reference Laplace factor $L_{\text{ref}, k}(\sigma) \ge 0$
satisfy the uniform upper bound and $O((2k)^{-\alpha})$ difference bound
$$(2k)^s \mathcal{L}_{2k}(\sigma) + L_{\text{ref}, k}(\sigma) \le M_{\text{raw}}, \qquad
  \bigl|(2k)^s \mathcal{L}_{2k}(\sigma) - L_{\text{ref}, k}(\sigma)\bigr|
    \le C_{\text{raw}} (2k)^{-\alpha}$$
for all $k \ge 1$, where $e^{-\Delta_\phi \sigma} L_{\text{ref}, k}(\sigma)$ is the Laplace
transform of a $\mathbb{Z}$-supported measure $\nu_k$ whose pairing with
$u \mapsto \varphi(\Delta_\phi + u)$ equals $P_{\text{ref}, k}(\varphi)$.

Then for every $\gamma \le \alpha \cdot \operatorname{midpointHarmonicExp}(A, 2\pi)$ and every
support radius $N \in \mathbb{N}$, there exists $C > 0$ such that for all $k \ge 1$ and all $C^2$
test functions $\varphi : \mathbb{R} \to \mathbb{R}$ supported in $[-N, N]$ with
$\|\varphi\|_\infty, \|\varphi'\|_\infty, \|\varphi''\|_\infty \le M_\varphi$,
$$\bigl|(2k)^s \langle \mu_{2k}, \varphi \rangle - P_{\text{ref}, k}(\varphi)\bigr|
  \le C \thinspace (2k)^{-\gamma} M_\varphi.$$ -/
theorem exists_const_abs_rescaled_pairSpin_sub_le
    {A Δ_phi s α γ M_raw C_raw : ℝ}
    (hA : 1 < A) (hα : 0 < α) (hθ_ge : γ ≤ α * midpointHarmonicExp A (2 * π))
    (hM_raw : 0 < M_raw) (hC_raw : 0 < C_raw) (N : ℕ)
    (ν : ℕ → Measure ℝ) (L_ref : ℕ → ℝ → ℝ) (P_ref : ℕ → (ℝ → ℝ) → ℝ)
    (hν_int : ∀ k, ν k (univ \ range (Int.cast : ℤ → ℝ)) = 0)
    (hν_exp : ∀ k {σ : ℝ}, σ < 0 → Integrable (fun u => Real.exp (σ * u)) (ν k))
    (hν_lap : ∀ k {σ : ℝ}, σ < 0 →
      laplaceTransformReal (ν k) σ = Real.exp (-Δ_phi * σ) * L_ref k σ)
    (hL_nonneg : ∀ k {σ : ℝ}, σ < 0 → 0 ≤ L_ref k σ)
    (hν_pair : ∀ k {φ : ℝ → ℝ}, Continuous φ → (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      ∫ u : ℝ, shiftedTest Δ_phi φ u ∂(ν k) = P_ref k φ)
    (h_raw : ∀ {k : ℕ}, 1 ≤ k → ∀ σ ∈ Icc (1 - 2 * A) (-1),
      (2 * (k : ℝ)) ^ s * M.laplaceSpinReal (2 * (k : ℤ)) σ + L_ref k σ ≤ M_raw ∧
      |(2 * (k : ℝ)) ^ s * M.laplaceSpinReal (2 * (k : ℤ)) σ - L_ref k σ| ≤
        C_raw * (2 * (k : ℝ)) ^ (-α)) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      Differentiable ℝ φ → Differentiable ℝ (deriv φ) →
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      0 ≤ M_φ →
      (∀ h, |φ h| ≤ M_φ) → (∀ h, |deriv φ h| ≤ M_φ) →
      (∀ h, |deriv (deriv φ) h| ≤ M_φ) →
      |(2 * (k : ℝ)) ^ s * M.pairSpin (2 * (k : ℤ)) φ - P_ref k φ| ≤
        C * (2 * (k : ℝ)) ^ (-γ) * M_φ := by
  have hσ_plus : (-1 : ℝ) < 0 := by norm_num
  set E_A : ℝ := Real.exp (|Δ_phi| * (2 * A - 1))
  have hEA_pos : 0 < E_A := Real.exp_pos _
  have hexp_le : ∀ {σ : ℝ}, σ ∈ Icc (1 - 2 * A) (-1) → Real.exp (-Δ_phi * σ) ≤ E_A := by
    intro σ hσ
    refine Real.exp_le_exp.mpr ?_
    have h_abs := le_abs_self (-Δ_phi * σ)
    rw [abs_mul, abs_neg, abs_of_neg (lt_of_le_of_lt hσ.2 hσ_plus)] at h_abs
    have h_nonneg : 0 ≤ |Δ_phi| := abs_nonneg Δ_phi
    have h_le : -σ ≤ 2 * A - 1 := by linarith [hσ.1]
    exact h_abs.trans (mul_le_mul_of_nonneg_left h_le h_nonneg)
  set M_A : ℝ := E_A * M_raw
  have hMA_pos : 0 < M_A := mul_pos hEA_pos hM_raw
  set C_A : ℝ := E_A * C_raw
  have hCA_pos : 0 < C_A := mul_pos hEA_pos hC_raw
  set N_shift : ℕ := N + ⌈|Δ_phi|⌉₊
  obtain ⟨C, hC_pos, h_taub_gen⟩ :=
    exists_const_abs_integral_sub_le_rpow hA hα hθ_ge hCA_pos hMA_pos N_shift
  refine ⟨C, hC_pos, fun {k} hk1 {φ} {M_φ} hφ hφ' hsupp hM_φ hφ0 hφ1 hφ2 => ?_⟩
  have h2k_ge1 : (1 : ℝ) ≤ 2 * (k : ℝ) := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    linarith
  have hM_bd : ∀ σ ∈ Icc (1 - 2 * A) (-1),
      laplaceTransformReal (M.rescaledShiftedMeasure s Δ_phi k) σ +
        laplaceTransformReal (ν k) σ ≤ M_A := by
    intro σ hσ
    have hσ_neg : σ < 0 := lt_of_le_of_lt hσ.2 hσ_plus
    rw [M.laplaceTransformReal_rescaledShiftedMeasure s Δ_phi k σ, hν_lap k hσ_neg, ← mul_add]
    have h_sum_nonneg :
        0 ≤ (2 * (k : ℝ)) ^ s * M.laplaceSpinReal (2 * (k : ℤ)) σ + L_ref k σ :=
      add_nonneg (mul_nonneg (by positivity) (M.laplaceSpinReal_nonneg _ _)) (hL_nonneg k hσ_neg)
    exact mul_le_mul (hexp_le hσ) (h_raw hk1 σ hσ).1 h_sum_nonneg hEA_pos.le
  have hδ_bd : ∀ σ ∈ Icc (1 - 2 * A) (-1),
      |laplaceTransformReal (M.rescaledShiftedMeasure s Δ_phi k) σ -
        laplaceTransformReal (ν k) σ| ≤ C_A * (2 * (k : ℝ)) ^ (-α) := by
    intro σ hσ
    have hσ_neg : σ < 0 := lt_of_le_of_lt hσ.2 hσ_plus
    rw [M.laplaceTransformReal_rescaledShiftedMeasure s Δ_phi k σ, hν_lap k hσ_neg,
      ← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-Δ_phi * σ) *
          |(2 * (k : ℝ)) ^ s * M.laplaceSpinReal (2 * (k : ℤ)) σ - L_ref k σ|
        ≤ E_A * (C_raw * (2 * (k : ℝ)) ^ (-α)) :=
          mul_le_mul (hexp_le hσ) (h_raw hk1 σ hσ).2 (abs_nonneg _) hEA_pos.le
      _ = C_A * (2 * (k : ℝ)) ^ (-α) := by dsimp [C_A]; ring
  have h_est := h_taub_gen h2k_ge1 (hν_int k)
    (M.integrable_exp_rescaledShiftedMeasure s Δ_phi k (by linarith))
    (M.integrable_exp_rescaledShiftedMeasure s Δ_phi k hσ_plus)
    (hν_exp k (by linarith))
    (hν_exp k hσ_plus)
    hM_bd hδ_bd
    (differentiable_shiftedTest Δ_phi hφ)
    (differentiable_deriv_shiftedTest Δ_phi hφ hφ')
    (fun u hu => shiftedTest_eq_zero_of_support Δ_phi hsupp hu)
    hM_φ
    (fun u => hφ0 (Δ_phi + u))
    (fun u => by rw [deriv_shiftedTest Δ_phi hφ]; exact hφ1 (Δ_phi + u))
    (fun u => by rw [deriv2_shiftedTest Δ_phi hφ hφ']; exact hφ2 (Δ_phi + u))
  rwa [M.integral_shiftedTest_rescaledShiftedMeasure s Δ_phi k hφ.continuous,
    hν_pair k hφ.continuous hsupp] at h_est

/-!
## 2. Quantitative Monomial Lightcone Bootstrap ($\Delta_\phi > 1/2$)

We now specialize Section 1 to the untransmuted radial monomial expansion ($s = 1 - 2\Delta_\phi$)
by combining `exists_const_abs_rescaled_pairSpin_sub_le` with the uniform Laplace bounds on
$[1 - 2A, -1]$ proved in `CFT.LightconeBootstrap.Monomial.LaplaceBound`
(`exists_uniform_laplaceSpinReal_sub_identity_bounds`). We state the results first for any abstract
`M : MonomialFourPointData` agreeing with `corr : FourPointData ν Δ_phi` on
$\operatorname{UcPdisk}$, and then directly for `corr.toMonomialFourPointData hν`.
-/

/-- **Main Quantitative Monomial Lightcone Bootstrap Against the Exact $t$-Channel Identity
(`MonomialFourPointData` version)**:
Let `M` be a radial monomial decomposition agreeing with `corr : FourPointData ν Δ_phi`
($\nu \ge 0$, $\Delta_\phi > 1/2$) on $\operatorname{UcPdisk}$ and having a twist gap
$h_{\text{gap}} > 0$ (`M.HasTwistGap h_gap`).
For any target rate
$$0 < \gamma < \min(2 h_{\text{gap}},\thinspace 2\Delta_\phi - 1)$$
and support radius $N \in \mathbb{N}$, there exists $C > 0$ such that for all $k \ge 1$ and all
$C^2$ test functions $\varphi$ supported in $[-N, N]$ with
$\|\varphi\|_\infty, \|\varphi'\|_\infty, \|\varphi''\|_\infty \le M_\varphi$,
$$\bigl|(2k)^{1 - 2\Delta_\phi} \langle \mu_{2k}, \varphi \rangle -
  (2k)^{1 - 2\Delta_\phi} \operatorname{identityMonomialPairing}(\Delta_\phi, 2k, \varphi)\bigr|
  \le C \thinspace (2k)^{-\gamma} M_\varphi.$$
Because `identityMonomialPairing` retains the exact finite-spin binomial coefficients of the
$t$-channel identity exchange, this comparison is free of any $O(k^{-1})$ Stirling error. -/
theorem exists_const_abs_pairSpin_sub_identity_le {ν Δ_phi h_gap γ : ℝ}
    (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν) (hΔ : 1 / 2 < Δ_phi)
    (hM : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      M.eval wl wr = corr.correlator_pdisk wl wr)
    (hgap : M.HasTwistGap h_gap)
    (hγ_pos : 0 < γ) (hγ_lt : γ < min (2 * h_gap) (2 * Δ_phi - 1))
    (N : ℕ) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      Differentiable ℝ φ → Differentiable ℝ (deriv φ) →
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      0 ≤ M_φ →
      (∀ h, |φ h| ≤ M_φ) → (∀ h, |deriv φ h| ≤ M_φ) →
      (∀ h, |deriv (deriv φ) h| ≤ M_φ) →
      |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.pairSpin (2 * (k : ℤ)) φ -
        (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityMonomialPairing Δ_phi (2 * k) φ| ≤
        C * (2 * (k : ℝ)) ^ (-γ) * M_φ := by
  have hΔ_pos : 0 < Δ_phi := by linarith
  have hγ_2h : γ < 2 * h_gap := lt_of_lt_of_le hγ_lt (min_le_left _ _)
  have hγ_rest : γ < 2 * Δ_phi - 1 := lt_of_lt_of_le hγ_lt (min_le_right _ _)
  set h' : ℝ := if 2 * (h_gap - Δ_phi) = -1 then (γ / 2 + h_gap) / 2 else h_gap
  have hh'_pos : 0 < h' := by dsimp [h']; split_ifs <;> linarith
  have hh'_le : h' ≤ h_gap := by dsimp [h']; split_ifs <;> linarith
  have hγ_2h' : γ < 2 * h' := by dsimp [h']; split_ifs <;> linarith
  have hh'_ne : 2 * (h' - Δ_phi) ≠ -1 := by
    dsimp [h']; split_ifs with h_eq <;> [linarith; exact h_eq]
  have hgap' : M.HasTwistGap h' := hgap.mono hh'_pos hh'_le
  set α : ℝ := min (2 * h') (2 * Δ_phi - 1)
  have hγα : γ < α := lt_min hγ_2h' hγ_rest
  have hα_pos : 0 < α := lt_trans hγ_pos hγα
  obtain ⟨A, hA, hθ_ge⟩ := exists_gt_one_le_mul_midpointHarmonicExp hα_pos hγα
  obtain ⟨_, M_raw, hM_raw_pos, C_raw, hC_raw_pos, h_raw⟩ :=
    M.exists_uniform_laplaceSpinReal_sub_identity_bounds corr hν hΔ hM hgap' hh'_ne
      (by linarith : 1 - 2 * A ≤ -1) (by norm_num : (-1 : ℝ) < 0)
  exact M.exists_const_abs_rescaled_pairSpin_sub_le hA hα_pos hθ_ge hM_raw_pos hC_raw_pos N
    (identityShiftedMeasure Δ_phi)
    (fun k σ => (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityLaplaceReal Δ_phi (2 * k) σ)
    (fun k φ => (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityMonomialPairing Δ_phi (2 * k) φ)
    (identityShiftedMeasure_compl_intCast_eq_zero Δ_phi)
    (fun k _ hσ => integrable_exp_identityShiftedMeasure hΔ_pos k hσ)
    (fun k _ hσ => laplaceTransformReal_identityShiftedMeasure hΔ_pos k hσ)
    (fun k _ _ => mul_nonneg (by positivity) (identityLaplaceReal_nonneg hΔ_pos (2 * k) _))
    (fun k _ hφ hsupp => integral_shiftedTest_identityShiftedMeasure hΔ_pos k N hφ hsupp)
    (fun hk1 _ hσ => h_raw hk1 hσ)

/-- Version of `exists_const_abs_pairSpin_sub_identity_le` assuming `ContDiff ℝ 2 φ`. -/
theorem exists_const_abs_pairSpin_sub_identity_le_contDiff {ν Δ_phi h_gap γ : ℝ}
    (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν) (hΔ : 1 / 2 < Δ_phi)
    (hM : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      M.eval wl wr = corr.correlator_pdisk wl wr)
    (hgap : M.HasTwistGap h_gap)
    (hγ_pos : 0 < γ) (hγ_lt : γ < min (2 * h_gap) (2 * Δ_phi - 1))
    (N : ℕ) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      ContDiff ℝ 2 φ →
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      0 ≤ M_φ →
      (∀ h, |φ h| ≤ M_φ) → (∀ h, |deriv φ h| ≤ M_φ) →
      (∀ h, |deriv (deriv φ) h| ≤ M_φ) →
      |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.pairSpin (2 * (k : ℤ)) φ -
        (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityMonomialPairing Δ_phi (2 * k) φ| ≤
        C * (2 * (k : ℝ)) ^ (-γ) * M_φ := by
  obtain ⟨C, hC_pos, hC⟩ :=
    M.exists_const_abs_pairSpin_sub_identity_le corr hν hΔ hM hgap hγ_pos hγ_lt N
  refine ⟨C, hC_pos, fun {k} hk1 {φ} {M_φ} hφ hsupp hM_φ hφ0 hφ1 hφ2 => ?_⟩
  have hφ_diff : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hφ_succ : ContDiff ℝ (1 + 1) φ := hφ
  have hφ'_diff : Differentiable ℝ (deriv φ) :=
    ((contDiff_succ_iff_deriv.mp hφ_succ).2.2).differentiable (by norm_num)
  exact hC hk1 hφ_diff hφ'_diff hsupp hM_φ hφ0 hφ1 hφ2

/-- **Quantitative Monomial Lightcone Bootstrap Against the Universal Gamma Pairing
(`MonomialFourPointData` version)**:
Combining the $O(k^{-1})$-free theorem `exists_const_abs_pairSpin_sub_identity_le` with the
kinematic Stirling expansion `exists_const_abs_identityMonomialPairing_sub_universal_le`
$$\bigl|(2k)^{1 - 2\Delta_\phi} \operatorname{identityMonomialPairing}(\Delta_\phi, 2k, \varphi) -
  \operatorname{universalMonomialPairing}(\Delta_\phi, \varphi)\bigr|
  \le C_0 \thinspace (2k)^{-1} M_\varphi$$
yields the quantitative bound against the $k$-independent limit
`universalMonomialPairing Δ_phi φ` for every target exponent
$$0 < \gamma < \min\bigl(2 h_{\text{gap}},\thinspace \min(1,\thinspace 2\Delta_\phi - 1)\bigr).$$ -/
theorem exists_const_abs_pairSpin_sub_universal_le {ν Δ_phi h_gap γ : ℝ}
    (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν) (hΔ : 1 / 2 < Δ_phi)
    (hM : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      M.eval wl wr = corr.correlator_pdisk wl wr)
    (hgap : M.HasTwistGap h_gap)
    (hγ_pos : 0 < γ) (hγ_lt : γ < min (2 * h_gap) (min 1 (2 * Δ_phi - 1)))
    (N : ℕ) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      Differentiable ℝ φ → Differentiable ℝ (deriv φ) →
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      0 ≤ M_φ →
      (∀ h, |φ h| ≤ M_φ) → (∀ h, |deriv φ h| ≤ M_φ) →
      (∀ h, |deriv (deriv φ) h| ≤ M_φ) →
      |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.pairSpin (2 * (k : ℤ)) φ -
        universalMonomialPairing Δ_phi φ| ≤ C * (2 * (k : ℝ)) ^ (-γ) * M_φ := by
  have hΔ_pos : 0 < Δ_phi := by linarith
  have hγ_lt_id : γ < min (2 * h_gap) (2 * Δ_phi - 1) :=
    lt_of_lt_of_le hγ_lt (min_le_min le_rfl (min_le_right 1 (2 * Δ_phi - 1)))
  have hγ_le_one : γ ≤ 1 :=
    ((lt_of_lt_of_le hγ_lt (min_le_right _ _)).trans_le (min_le_left 1 (2 * Δ_phi - 1))).le
  obtain ⟨C₁, hC₁_pos, hC₁⟩ :=
    M.exists_const_abs_pairSpin_sub_identity_le corr hν hΔ hM hgap hγ_pos hγ_lt_id N
  obtain ⟨C₂, hC₂_pos, hC₂⟩ :=
    exists_const_abs_identityMonomialPairing_sub_universal_le hΔ_pos N
  refine ⟨C₁ + C₂, add_pos hC₁_pos hC₂_pos,
    fun {k} hk1 {φ} {M_φ} hφ hφ' hsupp hM_φ hφ0 hφ1 hφ2 => ?_⟩
  have h2k_ge1 : (1 : ℝ) ≤ 2 * (k : ℝ) := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    linarith
  have hr_one : (2 * (k : ℝ))⁻¹ ≤ (2 * (k : ℝ)) ^ (-γ) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le h2k_ge1 (by linarith)
  have h_b1 := hC₁ hk1 hφ hφ' hsupp hM_φ hφ0 hφ1 hφ2
  have h_b2 := (hC₂ hk1 hsupp hM_φ hφ0).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr_one hC₂_pos.le) hM_φ)
  calc
    |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.pairSpin (2 * (k : ℤ)) φ -
        universalMonomialPairing Δ_phi φ|
      = |((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.pairSpin (2 * (k : ℤ)) φ -
            (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityMonomialPairing Δ_phi (2 * k) φ) +
          ((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityMonomialPairing Δ_phi (2 * k) φ -
            universalMonomialPairing Δ_phi φ)| := by ring_nf
    _ ≤ |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.pairSpin (2 * (k : ℤ)) φ -
            (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityMonomialPairing Δ_phi (2 * k) φ| +
          |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * identityMonomialPairing Δ_phi (2 * k) φ -
            universalMonomialPairing Δ_phi φ| := abs_add_le _ _
    _ ≤ C₁ * (2 * (k : ℝ)) ^ (-γ) * M_φ + C₂ * (2 * (k : ℝ)) ^ (-γ) * M_φ :=
        add_le_add h_b1 h_b2
    _ = (C₁ + C₂) * (2 * (k : ℝ)) ^ (-γ) * M_φ := by ring

/-- Version of `exists_const_abs_pairSpin_sub_universal_le` assuming `ContDiff ℝ 2 φ`. -/
theorem exists_const_abs_pairSpin_sub_universal_le_contDiff {ν Δ_phi h_gap γ : ℝ}
    (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν) (hΔ : 1 / 2 < Δ_phi)
    (hM : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      M.eval wl wr = corr.correlator_pdisk wl wr)
    (hgap : M.HasTwistGap h_gap)
    (hγ_pos : 0 < γ) (hγ_lt : γ < min (2 * h_gap) (min 1 (2 * Δ_phi - 1)))
    (N : ℕ) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      ContDiff ℝ 2 φ →
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      0 ≤ M_φ →
      (∀ h, |φ h| ≤ M_φ) → (∀ h, |deriv φ h| ≤ M_φ) →
      (∀ h, |deriv (deriv φ) h| ≤ M_φ) →
      |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.pairSpin (2 * (k : ℤ)) φ -
        universalMonomialPairing Δ_phi φ| ≤ C * (2 * (k : ℝ)) ^ (-γ) * M_φ := by
  obtain ⟨C, hC_pos, hC⟩ :=
    M.exists_const_abs_pairSpin_sub_universal_le corr hν hΔ hM hgap hγ_pos hγ_lt N
  refine ⟨C, hC_pos, fun {k} hk1 {φ} {M_φ} hφ hsupp hM_φ hφ0 hφ1 hφ2 => ?_⟩
  have hφ_diff : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hφ_succ : ContDiff ℝ (1 + 1) φ := hφ
  have hφ'_diff : Differentiable ℝ (deriv φ) :=
    ((contDiff_succ_iff_deriv.mp hφ_succ).2.2).differentiable (by norm_num)
  exact hC hk1 hφ_diff hφ'_diff hsupp hM_φ hφ0 hφ1 hφ2

end MonomialFourPointData

namespace FourPointData

variable {ν Δ_phi : ℝ} (corr : FourPointData ν Δ_phi)

/-- **Main Quantitative Monomial Lightcone Bootstrap Against the Exact $t$-Channel Identity
(`FourPointData` version)**:
For any reflection-positive four-point function `corr : FourPointData ν Δ_phi` with $\nu \ge 0$,
$\Delta_\phi > 1/2$, and a primary-spectrum twist gap `corr.HasTwistGap h_gap`
($h_{\text{gap}} > 0$), the canonical radial monomial decomposition
`corr.toMonomialFourPointData hν` satisfies
$$\bigl|(2k)^{1 - 2\Delta_\phi}
    \langle (\operatorname{corr.toMonomialFourPointData}\thinspace h\nu).\mu_{2k}, \varphi \rangle -
  (2k)^{1 - 2\Delta_\phi} \operatorname{identityMonomialPairing}(\Delta_\phi, 2k, \varphi)\bigr|
  \le C \thinspace (2k)^{-\gamma} M_\varphi$$
for every target rate $0 < \gamma < \min(2 h_{\text{gap}},\thinspace 2\Delta_\phi - 1)$,
uniformly over $k \ge 1$ and $C^2$ test functions $\varphi$ supported in $[-N, N]$. -/
theorem exists_const_abs_pairSpin_sub_identity_le {h_gap γ : ℝ}
    (hν : 0 ≤ ν) (hΔ : 1 / 2 < Δ_phi)
    (hgap : corr.HasTwistGap h_gap)
    (hγ_pos : 0 < γ) (hγ_lt : γ < min (2 * h_gap) (2 * Δ_phi - 1))
    (N : ℕ) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      ContDiff ℝ 2 φ →
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      0 ≤ M_φ →
      (∀ h, |φ h| ≤ M_φ) → (∀ h, |deriv φ h| ≤ M_φ) →
      (∀ h, |deriv (deriv φ) h| ≤ M_φ) →
      |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) *
          (corr.toMonomialFourPointData hν).pairSpin (2 * (k : ℤ)) φ -
        (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) *
          identityMonomialPairing Δ_phi (2 * k) φ| ≤ C * (2 * (k : ℝ)) ^ (-γ) * M_φ :=
  (corr.toMonomialFourPointData hν).exists_const_abs_pairSpin_sub_identity_le_contDiff
    corr hν hΔ (fun hwl hwr => corr.toMonomialFourPointData_eval hν hwl hwr)
    (hgap.toMonomialFourPointData hν) hγ_pos hγ_lt N

/-- **Quantitative Monomial Lightcone Bootstrap Against the Universal Gamma Pairing
(`FourPointData` version)**:
For any reflection-positive four-point function `corr : FourPointData ν Δ_phi` with $\nu \ge 0$,
$\Delta_\phi > 1/2$, and a primary-spectrum twist gap `corr.HasTwistGap h_gap`
($h_{\text{gap}} > 0$), the canonical radial monomial decomposition
`corr.toMonomialFourPointData hν` satisfies
$$\bigl|(2k)^{1 - 2\Delta_\phi}
    \langle (\operatorname{corr.toMonomialFourPointData}\thinspace h\nu).\mu_{2k}, \varphi \rangle -
  \operatorname{universalMonomialPairing}(\Delta_\phi, \varphi)\bigr|
  \le C \thinspace (2k)^{-\gamma} M_\varphi$$
for every target rate
$0 < \gamma < \min\bigl(2 h_{\text{gap}},\thinspace \min(1,\thinspace 2\Delta_\phi - 1)\bigr)$,
uniformly over $k \ge 1$ and $C^2$ test functions $\varphi$ supported in $[-N, N]$. -/
theorem exists_const_abs_pairSpin_sub_universal_le {h_gap γ : ℝ}
    (hν : 0 ≤ ν) (hΔ : 1 / 2 < Δ_phi)
    (hgap : corr.HasTwistGap h_gap)
    (hγ_pos : 0 < γ) (hγ_lt : γ < min (2 * h_gap) (min 1 (2 * Δ_phi - 1)))
    (N : ℕ) :
    ∃ C > 0, ∀ {k : ℕ}, 1 ≤ k →
      ∀ {φ : ℝ → ℝ} {M_φ : ℝ},
      ContDiff ℝ 2 φ →
      (∀ h : ℝ, (N : ℝ) < |h| → φ h = 0) →
      0 ≤ M_φ →
      (∀ h, |φ h| ≤ M_φ) → (∀ h, |deriv φ h| ≤ M_φ) →
      (∀ h, |deriv (deriv φ) h| ≤ M_φ) →
      |(2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) *
          (corr.toMonomialFourPointData hν).pairSpin (2 * (k : ℤ)) φ -
        universalMonomialPairing Δ_phi φ| ≤ C * (2 * (k : ℝ)) ^ (-γ) * M_φ :=
  (corr.toMonomialFourPointData hν).exists_const_abs_pairSpin_sub_universal_le_contDiff
    corr hν hΔ (fun hwl hwr => corr.toMonomialFourPointData_eval hν hwl hwr)
    (hgap.toMonomialFourPointData hν) hγ_pos hγ_lt N

end FourPointData
