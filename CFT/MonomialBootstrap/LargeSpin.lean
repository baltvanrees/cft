/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Balt van Rees
-/
import CFT.MonomialBootstrap.IdentityProj
import CFT.Vitali

/-!
# Large-Spin Universality in the Monomial Lightcone Bootstrap

This file formalizes Step 4 of the monomial lightcone bootstrap via the single-variable spin-$J$
Laplace transform $L_J(w) = \int_{\mathbb{R}} e^{h w} \, d\mu_J(h)$ (`laplaceSpin`):

1. **Stage 1: Real-Axis Asymptotics of $L_{2k}(\sigma)$ (`tendsto_laplaceSpinReal_of_half_lt` and
   `tendsto_laplaceSpinReal`)**:
   For real $\sigma < 0$ and even spin $J = 2k > 0$, we choose real contour parameters
   $$\sigma_r(2k) = -\frac{1}{2k} < 0, \qquad \sigma_l(2k) = \sigma + \frac{1}{2k} < 0$$
   in `laplaceSpinReal_eq_fourierProjSpin`:
   $$L_{2k}(\sigma) = \int_{-\pi/2}^{\pi/2} \frac{d\theta}{\pi} \,
     e^{-2k (\sigma_r + i\theta)} \,
     \mathcal{G}_{\text{mon}}(\sigma_l - i\theta,\, \sigma_r + i\theta).$$
   Because $\sigma_l$ and $\sigma_r$ are real, both arguments $\sigma_l - i\theta$ and
   $\sigma_r + i\theta$ have imaginary parts in $[-\pi/2, \pi/2] \subset (-\pi, \pi)$ for all
   $\theta \in [-\pi/2, \pi/2]$, staying strictly inside the $t$-channel $\rho$-polydisk.
   Splitting $\mathcal{G}_{\text{mon}}$ into the $t$-channel identity `crossIdentity` and the
   twist-gap remainder (`norm_eval_sub_crossIdentity_le` from `Gap.lean`) shows that for all
   $\sigma < 0$:
   $$\lim_{k \to \infty} (2k)^{1 - 2\Delta_\phi} L_{2k}(\sigma) =
     \operatorname{universalLaplaceReal}(\Delta_\phi, \sigma) :=
     \frac{2 \cdot 4^{\Delta_\phi}}{\Gamma(2\Delta_\phi)}
     \operatorname{crossFactor}(\Delta_\phi, \sigma).$$

2. **Stage 2: Complex Extension to $w \in \operatorname{UcDisk}$ via 1D Vitali's Theorem
   (`tendsto_laplaceSpin_of_half_lt` and `tendsto_laplaceSpin`)**:
   By the 1D positivity bound `norm_laplaceSpin_le_laplaceSpinReal` (`MonomialDecomp.lean`),
   $$\|L_{2k}(\sigma + i t)\| \le L_{2k}(\sigma) \qquad
     \forall \sigma < 0, \; \forall t \in \mathbb{R}.$$
   Since $(2k)^{1 - 2\Delta_\phi} L_{2k}(w)$ is holomorphic on $w \in \operatorname{UcDisk}$,
   uniformly bounded on every vertical line $\operatorname{Re}(w) = \sigma < 0$ (and on compact
   subsets of $\operatorname{UcDisk}$) by $(2k)^{1 - 2\Delta_\phi} L_{2k}(\sigma)$, and converges
   on the negative real axis $\sigma < 0$, Vitali's theorem upgrades convergence to all
   $w \in \operatorname{UcDisk}$.

3. **Stage 3: Pairing with $\varphi(h)$ via Vertical Contour Integration
   (`tendsto_pairSpin_large_even_spin_of_half_lt` and `tendsto_pairSpin_large_even_spin`)**:
   Using `pairSpin_eq_integral_laplaceSpin` at $\sigma = -1 < 0$ and Dominated Convergence along
   $w = \sigma + i t$ (dominated uniformly in $t \in \mathbb{R}$ by the $t$-independent bound
   $(2k)^{1 - 2\Delta_\phi} L_{2k}(\sigma) \, \|\widehat{\varphi}_\sigma(t)\|$) together with
   `integral_laplaceFourierTransform_mul_universalLaplace` (`IdentityProj.lean`) yields the
   universal large-spin asymptotics of $\int_{\mathbb{R}} \varphi(h) \, d\mu_{2k}(h)$.
-/

open Real Complex Topology Set Metric MeasureTheory Filter
open scoped ComplexConjugate

namespace MonomialFourPointData

variable (M : MonomialFourPointData)

/-!
## Stage 1: Real-Axis Asymptotics of $L_{2k}(\sigma)$ via the Folded $\theta$-Integral
-/

/-- **$L^1$ Modulus Bound on the Folded $\theta$-Contour $[-\pi/2, \pi/2]$**:
Integrating `norm_eval_sub_crossIdentity_le` over $\theta \in [-\pi/2, \pi/2]$ bounds the
rescaled remainder for any non-resonant twist gap $2(h_{\text{gap}} - \Delta_\phi) \ne -1$ by the
lightcone peak contribution $O((2k)^{-2 h_{\text{gap}}})$ near $\theta = 0$ plus the
$O((2k)^{1 - 2\Delta_\phi})$ bulk contribution away from $\theta = 0$. -/
theorem exists_bound_fourierProjSpin_sub_identity_real {ν Δ_phi h_gap : ℝ}
    (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi)
    (hM : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      M.eval wl wr = corr.correlator_pdisk wl wr)
    (hgap : M.HasTwistGap h_gap) (h_ne : 2 * (h_gap - Δ_phi) ≠ -1)
    {σ : ℝ} (hσ : σ < 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k : ℕ in atTop,
      ‖(((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) : ℝ) : ℂ) *
          (M.fourierProjSpin (2 * (k : ℤ))
              (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ)) -
            identityProjSpin Δ_phi (2 * (k : ℤ))
              (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ)))‖ ≤
        C * ((2 * (k : ℝ)) ^ (-2 * h_gap) + (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi)) := by
  have hh_gap : 0 < h_gap := by
    rcases hgap with ⟨_, hlow, _, _⟩
    exact hlow.h_gap_pos
  set σl0 := Real.log (1 - Real.sqrt 2 / 4 * Real.exp (σ / 2))
  set σr0 := Real.log (1 - Real.sqrt 2 / 4 * Real.exp (-1 / 2))
  have hsqrt2_lt : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hσl0_neg : σl0 < 0 := by
    dsimp [σl0]
    have h_prod_pos : 0 < Real.sqrt 2 / 4 * Real.exp (σ / 2) := by positivity
    have h_pos : 0 < 1 - Real.sqrt 2 / 4 * Real.exp (σ / 2) := by
      have : Real.exp (σ / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2), Real.exp_pos (σ / 2)]
    exact Real.log_neg h_pos (by linarith)
  have hσr0_neg : σr0 < 0 := by
    dsimp [σr0]
    have h_prod_pos : 0 < Real.sqrt 2 / 4 * Real.exp (-1 / 2) := by positivity
    have h_pos : 0 < 1 - Real.sqrt 2 / 4 * Real.exp (-1 / 2) := by
      have : Real.exp (-1 / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2), Real.exp_pos (-1 / 2)]
    exact Real.log_neg h_pos (by linarith)
  rcases integral_norm_one_sub_exp_rpow_le h_ne with ⟨C_int, hC_int_nonneg, hC_int⟩
  set K_left := (4 : ℝ) ^ Δ_phi * (1 - Real.exp (σ / 2)) ^ (-2 * Δ_phi)
  have h1_exp_σ2 : 0 < 1 - Real.exp (σ / 2) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hK_left_nonneg : 0 ≤ K_left := by positivity
  set K_rem := Real.exp (1 - h_gap * σr0) * K_left * (4 : ℝ) ^ Δ_phi * (M.evalReal σl0 σr0 - 1)
  have hK_rem_nonneg : 0 ≤ K_rem :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le hK_left_nonneg) (by positivity))
      (M.evalReal_sub_one_nonneg hgap σl0 σr0)
  refine ⟨π⁻¹ * K_rem * C_int, by positivity, ?_⟩
  have h_ev : ∀ᶠ k : ℕ in atTop, 1 ≤ k ∧ σ + 1 / (2 * (k : ℝ)) ≤ σ / 2 := by
    have h_tendsto : Tendsto (fun k : ℕ => σ + 1 / (2 * (k : ℝ))) atTop (𝓝 (σ + 0)) :=
      tendsto_const_nhds.add
        (tendsto_const_nhds.div_atTop
          (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_natCast_atTop_atTop))
    rw [add_zero] at h_tendsto
    exact (eventually_ge_atTop 1).and
      (h_tendsto.eventually (ge_mem_nhds (by linarith : σ < σ / 2)))
  filter_upwards [h_ev] with k ⟨hk1, hσk⟩
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have h2k_pos : (0 : ℝ) < 2 * (k : ℝ) := by positivity
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
    rw [mem_UcDisk_iff]; dsimp [wl0]; linarith
  have hwr0 : wr0 ∈ UcDisk := by
    rw [mem_UcDisk_iff]; dsimp [wr0]; simp [hε_pos]
  have h_sub_proj :
      M.fourierProjSpin (2 * (k : ℤ)) wl0 wr0 - identityProjSpin Δ_phi (2 * (k : ℤ)) wl0 wr0 =
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
      exact (h1.mul (continuous_crossIdentity_shift Δ_phi hwl0 hwr0)).intervalIntegrable _ _
  have h_wr0_eq : ((-1 / (2 * (k : ℝ)) : ℝ) : ℂ) = wr0 := by
    dsimp [wr0, ε]; ring_nf
  rw [h_wr0_eq, h_sub_proj, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (rpow_nonneg h2k_pos.le _)]
  have h_norm_pi : ‖(π : ℂ)⁻¹‖ = π⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [h_norm_pi]
  have h_cont_bound :
      Continuous (fun θ : ℝ =>
        K_rem * ‖1 - Complex.exp ((-ε : ℂ) + (θ : ℂ) * I)‖ ^ (2 * (h_gap - Δ_phi))) := by
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
          K_rem * ‖1 - Complex.exp ((-ε : ℂ) + (θ : ℂ) * I)‖ ^ (2 * (h_gap - Δ_phi)) := by
    refine intervalIntegral.norm_integral_le_of_norm_le (by linarith [Real.pi_pos])
      (Eventually.of_forall (fun θ hθ => ?_)) (h_cont_bound.intervalIntegrable _ _)
    have hθ_Icc : θ ∈ Icc (-π / 2) (π / 2) := ⟨hθ.1.le, hθ.2⟩
    have h_neg_θ_Icc : -θ ∈ Icc (-π / 2) (π / 2) := ⟨by linarith [hθ.2], by linarith [hθ.1.le]⟩
    set wl := wl0 - (θ : ℂ) * I
    set wr := wr0 + (θ : ℂ) * I
    have hwl : wl ∈ UcDisk := sub_I_mul_mem_UcDisk hwl0 θ
    have hwr : wr ∈ UcDisk := add_I_mul_mem_UcDisk hwr0 θ
    have hwl_im : wl.im ∈ Ioo (-π) π := by
      dsimp [wl, wl0]
      simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero, zero_sub,
        mem_Ioo, neg_lt_neg_iff]
      exact ⟨by linarith [hθ.2, Real.pi_pos], by linarith [hθ.1.le, Real.pi_pos]⟩
    have hwr_im : wr.im ∈ Ioo (-π) π := by
      dsimp [wr, wr0]
      simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero, zero_add,
        mem_Ioo]
      exact ⟨by linarith [hθ.1.le, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
    have hwl_cross : (crossW wl).re ≤ σl0 := by
      refine re_crossW_le_of_re_ge hwl ?_ ?_
      · dsimp [wl, wl0]; simp [hε_pos.le]
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
      dsimp [wl, wl0]; simpa using hσk
    have h_cf_r : ‖crossFactor Δ_phi wr‖ * Real.exp (h_gap * (crossW wr).re) ≤
        (4 : ℝ) ^ Δ_phi * ‖1 - Complex.exp ((-ε : ℂ) + (θ : ℂ) * I)‖ ^ (2 * (h_gap - Δ_phi)) := by
      have hwr_eq : wr = (-ε : ℂ) + (θ : ℂ) * I := by dsimp [wr, wr0]; push_cast; rfl
      rw [← hwr_eq]
      exact norm_crossFactor_mul_exp_re_crossW_le hΔ hh_gap hwr
        (by dsimp [wr, wr0]; simpa using hθ_Icc)
    have h_ci : ‖crossIdentity Δ_phi wl wr‖ *
        (Real.exp (h_gap * ((crossW wr).re - σr0)) * (M.evalReal σl0 σr0 - 1)) =
        (‖crossFactor Δ_phi wl‖ * (‖crossFactor Δ_phi wr‖ * Real.exp (h_gap * (crossW wr).re))) *
          (Real.exp (- (h_gap * σr0)) * (M.evalReal σl0 σr0 - 1)) := by
      dsimp [crossIdentity]
      rw [norm_mul, mul_sub h_gap, Real.exp_sub, div_eq_mul_inv, ← Real.exp_neg]
      ring
    rw [h_ci] at h_pt
    have h_prod_le :
        ‖crossFactor Δ_phi wl‖ * (‖crossFactor Δ_phi wr‖ * Real.exp (h_gap * (crossW wr).re)) ≤
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
      _ = K_rem * ‖1 - Complex.exp ((-ε : ℂ) + (θ : ℂ) * I)‖ ^ (2 * (h_gap - Δ_phi)) := by
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
    rw [one_div, Real.inv_rpow h2k_pos.le, ← Real.rpow_neg h2k_pos.le, ← Real.rpow_add h2k_pos]
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
        exact h_int_bound.trans (mul_le_mul_of_nonneg_left (hC_int hε_pos hε_le) hK_rem_nonneg)
    _ = (π⁻¹ * K_rem * C_int) *
          ((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * (ε ^ (2 * (h_gap - Δ_phi) + 1) + 1)) := by ring
    _ = (π⁻¹ * K_rem * C_int) *
          ((2 * (k : ℝ)) ^ (-2 * h_gap) + (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi)) := by
      rw [h_rpow_alg]

/-- **Short Proof of Remainder Vanishing for $\Delta_\phi > 1/2$**:
When $\Delta_\phi > 1/2$, both exponents $-2 h_{\text{gap}} < 0$ and $1 - 2\Delta_\phi < 0$ are
strictly negative, so the $L^1$ modulus bound `exists_bound_fourierProjSpin_sub_identity_real`
alone (without using phase cancellation away from $\theta = 0$) immediately implies that the
rescaled remainder tends to $0$ as $k \to \infty$. -/
theorem tendsto_fourierProjSpin_sub_identity_real_of_half_lt {ν Δ_phi h_gap : ℝ}
    (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν) (hΔ : 1 / 2 < Δ_phi)
    (hM : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      M.eval wl wr = corr.correlator_pdisk wl wr)
    (hgap : M.HasTwistGap h_gap)
    {σ : ℝ} (hσ : σ < 0) :
    Tendsto
      (fun k : ℕ =>
        (((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) : ℝ) : ℂ) *
          (M.fourierProjSpin (2 * (k : ℤ))
              (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ)) -
            identityProjSpin Δ_phi (2 * (k : ℤ))
              (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ))))
      atTop (𝓝 0) := by
  have hΔ_pos : 0 < Δ_phi := by linarith
  have hh_gap : 0 < h_gap := by
    rcases hgap with ⟨_, hlow, _, _⟩
    exact hlow.h_gap_pos
  set h' := if 2 * (h_gap - Δ_phi) = -1 then h_gap / 2 else h_gap
  have hh'_pos : 0 < h' := by
    dsimp [h']; split_ifs <;> linarith
  have hh'_le : h' ≤ h_gap := by
    dsimp [h']; split_ifs <;> linarith
  have hh'_ne : 2 * (h' - Δ_phi) ≠ -1 := by
    dsimp [h']
    split_ifs with h_eq
    · linarith
    · exact h_eq
  have hgap' : M.HasTwistGap h' := hgap.mono hh'_pos hh'_le
  rcases M.exists_bound_fourierProjSpin_sub_identity_real corr hν hΔ_pos hM hgap' hh'_ne hσ with
    ⟨C, _, hC⟩
  have h_2k : Tendsto (fun k : ℕ => 2 * (k : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_natCast_atTop_atTop
  have h_tendsto1 : Tendsto (fun k : ℕ => (2 * (k : ℝ)) ^ (-2 * h')) atTop (𝓝 0) := by
    have h_exp : -2 * h' = - (2 * h') := by ring
    rw [h_exp]
    exact (tendsto_rpow_neg_atTop (by linarith)).comp h_2k
  have h_tendsto2 : Tendsto (fun k : ℕ => (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi)) atTop (𝓝 0) := by
    have h_exp : 1 - 2 * Δ_phi = - (2 * Δ_phi - 1) := by ring
    rw [h_exp]
    exact (tendsto_rpow_neg_atTop (by linarith)).comp h_2k
  have h_zero :
      Tendsto (fun k : ℕ => C * ((2 * (k : ℝ)) ^ (-2 * h') + (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi)))
        atTop (𝓝 0) := by
    simpa using (h_tendsto1.add h_tendsto2).const_mul C
  exact squeeze_zero_norm' hC h_zero

/-- For $\Delta_\phi > 1/2$ and $\sigma < 0$, the rescaled real spin-$2k$ Laplace transform
$(2k)^{1 - 2\Delta_\phi} L_{2k}(\sigma)$ and the rescaled $t$-channel identity projection have
vanishing difference as $k \to \infty$ (proved with zero `sorry`s). -/
theorem tendsto_laplaceSpinReal_sub_identityProjSpin_of_half_lt {ν Δ_phi h_gap : ℝ}
    (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν) (hΔ : 1 / 2 < Δ_phi)
    (hM : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      M.eval wl wr = corr.correlator_pdisk wl wr)
    (hgap : M.HasTwistGap h_gap)
    {σ : ℝ} (hσ : σ < 0) :
    Tendsto
      (fun k : ℕ =>
        (((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ : ℝ) : ℂ) -
          (((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) : ℝ) : ℂ) *
            identityProjSpin Δ_phi (2 * (k : ℤ))
              (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ)))
      atTop (𝓝 0) := by
  have h_rem := M.tendsto_fourierProjSpin_sub_identity_real_of_half_lt corr hν hΔ hM hgap hσ
  have h_eventually : ∀ᶠ k : ℕ in atTop, 0 < k ∧ σ + 1 / (2 * (k : ℝ)) < 0 := by
    have h_tendsto : Tendsto (fun k : ℕ => σ + 1 / (2 * (k : ℝ))) atTop (𝓝 (σ + 0)) :=
      tendsto_const_nhds.add
        (tendsto_const_nhds.div_atTop
          (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_natCast_atTop_atTop))
    rw [add_zero] at h_tendsto
    exact (eventually_gt_atTop 0).and (h_tendsto.eventually (gt_mem_nhds hσ))
  refine h_rem.congr' ?_
  filter_upwards [h_eventually] with k ⟨hk, hσl⟩
  have hk_pos : (0 : ℝ) < 2 * (k : ℝ) := by positivity
  have hσr : -1 / (2 * (k : ℝ)) < 0 := div_neg_of_neg_of_pos (by norm_num) hk_pos
  have h_even : Even (2 * (k : ℤ)) := even_two_mul (k : ℤ)
  have h_eq := M.laplaceSpinReal_eq_fourierProjSpin h_even hσl hσr
  have h_add : (σ + 1 / (2 * (k : ℝ))) + (-1 / (2 * (k : ℝ))) = σ := by ring
  rw [h_add] at h_eq
  push_cast at h_eq ⊢
  rw [h_eq]
  ring

/-- **Stage 1 Explicit Asymptotic Theorem for $\Delta_\phi > 1/2$ (`sorry`-free)**:
For $\Delta_\phi > 1/2$ and every $\sigma < 0$, the rescaled real spin-$2k$ Laplace transform
$(2k)^{1 - 2\Delta_\phi} L_{2k}(\sigma)$ converges as $k \to \infty$ to
`universalLaplaceReal Δ_phi σ` (proved with zero `sorry`s). -/
theorem tendsto_laplaceSpinReal_of_half_lt {ν Δ_phi h_gap : ℝ}
    (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν) (hΔ : 1 / 2 < Δ_phi)
    (hM : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      M.eval wl wr = corr.correlator_pdisk wl wr)
    (hgap : M.HasTwistGap h_gap)
    {σ : ℝ} (hσ : σ < 0) :
    Tendsto
      (fun k : ℕ => (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ)
      atTop (𝓝 (universalLaplaceReal Δ_phi σ)) := by
  have hΔ_pos : 0 < Δ_phi := by linarith
  have h_id := tendsto_identityProjSpin_real hΔ_pos hσ
  have h_rem := M.tendsto_fourierProjSpin_sub_identity_real_of_half_lt corr hν hΔ hM hgap hσ
  have h_sum := h_rem.add h_id
  rw [zero_add] at h_sum
  have h_eventually : ∀ᶠ k : ℕ in atTop, 0 < k ∧ σ + 1 / (2 * (k : ℝ)) < 0 := by
    have h_tendsto : Tendsto (fun k : ℕ => σ + 1 / (2 * (k : ℝ))) atTop (𝓝 (σ + 0)) :=
      tendsto_const_nhds.add
        (tendsto_const_nhds.div_atTop
          (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_natCast_atTop_atTop))
    rw [add_zero] at h_tendsto
    exact (eventually_gt_atTop 0).and (h_tendsto.eventually (gt_mem_nhds hσ))
  have h_complex : Tendsto
      (fun k : ℕ =>
        (((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ : ℝ) : ℂ))
      atTop (𝓝 (universalLaplaceReal Δ_phi σ : ℂ)) := by
    refine h_sum.congr' ?_
    filter_upwards [h_eventually] with k ⟨hk, hσl⟩
    have hk_pos : (0 : ℝ) < 2 * (k : ℝ) := by positivity
    have hσr : -1 / (2 * (k : ℝ)) < 0 := div_neg_of_neg_of_pos (by norm_num) hk_pos
    have h_even : Even (2 * (k : ℤ)) := even_two_mul (k : ℤ)
    have h_eq := M.laplaceSpinReal_eq_fourierProjSpin h_even hσl hσr
    have h_add : (σ + 1 / (2 * (k : ℝ))) + (-1 / (2 * (k : ℝ))) = σ := by ring
    rw [h_add] at h_eq
    push_cast at h_eq ⊢
    rw [h_eq]
    ring
  simpa [Function.comp_def] using (Complex.continuous_re.tendsto _).comp h_complex

/-- **Vanishing of the Non-Identity Remainder on the Real-Axis $\theta$-Contour**:
For $\sigma < 0$, along $\sigma_r(2k) = -1/(2k)$ and $\sigma_l(2k) = \sigma + 1/(2k) < 0$, both
arguments $(\sigma_l - i\theta, \sigma_r + i\theta)$ stay inside the $t$-channel strip
$\operatorname{Im} \in [-\pi/2, \pi/2] \subset (-\pi, \pi)$ for all $\theta \in [-\pi/2, \pi/2]$,
and `norm_eval_sub_crossIdentity_le` shows that the rescaled difference between
`M.fourierProjSpin` and `identityProjSpin` tends to $0$ as $k \to \infty$. -/
theorem tendsto_fourierProjSpin_sub_identity_real {ν Δ_phi h_gap : ℝ}
    (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi)
    (hM : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      M.eval wl wr = corr.correlator_pdisk wl wr)
    (hgap : M.HasTwistGap h_gap)
    {σ : ℝ} (hσ : σ < 0) :
    Tendsto
      (fun k : ℕ =>
        (((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) : ℝ) : ℂ) *
          (M.fourierProjSpin (2 * (k : ℤ))
              (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ)) -
            identityProjSpin Δ_phi (2 * (k : ℤ))
              (((σ + 1 / (2 * (k : ℝ)) : ℝ) : ℂ)) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ))))
      atTop (𝓝 0) := by
  sorry

/-- **Stage 1 Theorem (Real-Axis Asymptotics of $L_{2k}(\sigma)$)**:
For every $\sigma < 0$, the rescaled real spin-$2k$ Laplace transform
$(2k)^{1 - 2\Delta_\phi} L_{2k}(\sigma)$ converges as $k \to \infty$ to
`universalLaplaceReal Δ_phi σ`. -/
theorem tendsto_laplaceSpinReal {ν Δ_phi h_gap : ℝ}
    (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi)
    (hM : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      M.eval wl wr = corr.correlator_pdisk wl wr)
    (hgap : M.HasTwistGap h_gap)
    {σ : ℝ} (hσ : σ < 0) :
    Tendsto
      (fun k : ℕ => (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ)
      atTop (𝓝 (universalLaplaceReal Δ_phi σ)) := by
  have h_id := tendsto_identityProjSpin_real hΔ hσ
  have h_rem := M.tendsto_fourierProjSpin_sub_identity_real corr hν hΔ hM hgap hσ
  have h_sum := h_rem.add h_id
  rw [zero_add] at h_sum
  have h_eventually : ∀ᶠ k : ℕ in atTop, 0 < k ∧ σ + 1 / (2 * (k : ℝ)) < 0 := by
    have h_tendsto : Tendsto (fun k : ℕ => σ + 1 / (2 * (k : ℝ))) atTop (𝓝 (σ + 0)) :=
      tendsto_const_nhds.add
        (tendsto_const_nhds.div_atTop
          (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_natCast_atTop_atTop))
    rw [add_zero] at h_tendsto
    exact (eventually_gt_atTop 0).and (h_tendsto.eventually (gt_mem_nhds hσ))
  have h_complex : Tendsto
      (fun k : ℕ =>
        (((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ : ℝ) : ℂ))
      atTop (𝓝 (universalLaplaceReal Δ_phi σ : ℂ)) := by
    refine h_sum.congr' ?_
    filter_upwards [h_eventually] with k ⟨hk, hσl⟩
    have hk_pos : (0 : ℝ) < 2 * (k : ℝ) := by positivity
    have hσr : -1 / (2 * (k : ℝ)) < 0 := div_neg_of_neg_of_pos (by norm_num) hk_pos
    have h_even : Even (2 * (k : ℤ)) := even_two_mul (k : ℤ)
    have h_eq := M.laplaceSpinReal_eq_fourierProjSpin h_even hσl hσr
    have h_add : (σ + 1 / (2 * (k : ℝ))) + (-1 / (2 * (k : ℝ))) = σ := by ring
    rw [h_add] at h_eq
    push_cast at h_eq ⊢
    rw [h_eq]
    ring
  simpa [Function.comp_def] using (Complex.continuous_re.tendsto _).comp h_complex

/-!
## Stage 2: Complex Extension to $w \in \operatorname{UcDisk}$ via 1D Vitali's Theorem
-/

/-- **1D Vertical-Line Positivity Bound on Rescaled `laplaceSpin`**:
For any $\sigma < 0$, $t \in \mathbb{R}$, and $k \in \mathbb{N}$, the modulus of the rescaled
spin-$2k$ Laplace transform at $w = \sigma + i t$ is bounded uniformly in $t$ by its real-axis
value at $\sigma$:
$$\left\|(2k)^{1 - 2\Delta_\phi} L_{2k}(\sigma + i t)\right\| \le
  (2k)^{1 - 2\Delta_\phi} L_{2k}(\sigma).$$ -/
theorem norm_rescaled_laplaceSpin_le (Δ_phi : ℝ) (k : ℕ) (σ t : ℝ) :
    ‖(((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) : ℝ) : ℂ) *
        M.laplaceSpin (2 * (k : ℤ)) ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (rpow_nonneg (by positivity) _)]
  have h_bound := M.norm_laplaceSpin_le_laplaceSpinReal (2 * (k : ℤ)) ((σ : ℂ) + (t : ℂ) * I)
  have h_re : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
  rw [h_re] at h_bound
  exact mul_le_mul_of_nonneg_left h_bound (rpow_nonneg (by positivity) _)

/-- **Stage 2 Explicit Asymptotic Theorem on `UcDisk` for $\Delta_\phi > 1/2$ (`sorry`-free)**:
For $\Delta_\phi > 1/2$, Vitali's theorem implies convergence of
$(2k)^{1 - 2\Delta_\phi} L_{2k}(w)$ at every $w \in \operatorname{UcDisk}$ to
`universalLaplace Δ_phi w` (proved with zero `sorry`s). -/
theorem tendsto_laplaceSpin_of_half_lt {ν Δ_phi h_gap : ℝ}
    (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν) (hΔ : 1 / 2 < Δ_phi)
    (hM : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      M.eval wl wr = corr.correlator_pdisk wl wr)
    (hgap : M.HasTwistGap h_gap)
    {w : ℂ} (hw : w ∈ UcDisk) :
    Tendsto
      (fun k : ℕ =>
        (((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) : ℝ) : ℂ) * M.laplaceSpin (2 * (k : ℤ)) w)
      atTop (𝓝 (universalLaplace Δ_phi w)) := by
  refine CFT.vitali_porter_ucDisk
    (Eventually.of_forall fun k : ℕ =>
      (M.differentiableOn_laplaceSpin (2 * (k : ℤ))).const_mul _)
    (differentiableOn_universalLaplace Δ_phi) ?_ ?_ hw
  · intro σ hσ
    refine ⟨universalLaplaceReal Δ_phi σ + 1, ?_⟩
    have h_real_lim := M.tendsto_laplaceSpinReal_of_half_lt corr hν hΔ hM hgap hσ
    have h_ev : ∀ᶠ k : ℕ in atTop,
        (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ <
          universalLaplaceReal Δ_phi σ + 1 :=
      h_real_lim.eventually (gt_mem_nhds (by linarith))
    filter_upwards [h_ev] with k hk z hz
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (rpow_nonneg (by positivity) _)]
    have h1 := M.norm_laplaceSpin_le_laplaceSpinReal (2 * (k : ℤ)) z
    have h2 := M.laplaceSpinReal_mono (2 * (k : ℤ)) (lt_trans hz hσ) hσ hz.le
    have h12 : ‖M.laplaceSpin (2 * (k : ℤ)) z‖ ≤ M.laplaceSpinReal (2 * (k : ℤ)) σ :=
      h1.trans h2
    calc
      (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * ‖M.laplaceSpin (2 * (k : ℤ)) z‖
        ≤ (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ :=
          mul_le_mul_of_nonneg_left h12 (rpow_nonneg (by positivity) _)
      _ ≤ universalLaplaceReal Δ_phi σ + 1 := hk.le
  · intro x hx
    rw [universalLaplace_ofReal Δ_phi hx]
    have h_real_lim :=
      (Complex.continuous_ofReal.tendsto _).comp
        (M.tendsto_laplaceSpinReal_of_half_lt corr hν hΔ hM hgap hx)
    refine h_real_lim.congr (fun k => ?_)
    dsimp [Function.comp_def]
    rw [Complex.ofReal_mul, M.laplaceSpin_ofReal]

/-- **Stage 2 Theorem (Complex Extension via 1D Vitali's Theorem on `UcDisk`)**:
Because $(2k)^{1 - 2\Delta_\phi} L_{2k}(w)$ is holomorphic on $w \in \operatorname{UcDisk}$,
uniformly bounded on vertical lines (and compact subsets of $\operatorname{UcDisk}$) by
`norm_rescaled_laplaceSpin_le` and `tendsto_laplaceSpinReal`, and converges on the negative real
axis $\sigma < 0$ (`tendsto_laplaceSpinReal`), Vitali's theorem implies convergence at every
$w \in \operatorname{UcDisk}$ to `universalLaplace Δ_phi w`. -/
theorem tendsto_laplaceSpin {ν Δ_phi h_gap : ℝ}
    (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi)
    (hM : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      M.eval wl wr = corr.correlator_pdisk wl wr)
    (hgap : M.HasTwistGap h_gap)
    {w : ℂ} (hw : w ∈ UcDisk) :
    Tendsto
      (fun k : ℕ =>
        (((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) : ℝ) : ℂ) * M.laplaceSpin (2 * (k : ℤ)) w)
      atTop (𝓝 (universalLaplace Δ_phi w)) := by
  refine CFT.vitali_porter_ucDisk
    (Eventually.of_forall fun k : ℕ =>
      (M.differentiableOn_laplaceSpin (2 * (k : ℤ))).const_mul _)
    (differentiableOn_universalLaplace Δ_phi) ?_ ?_ hw
  · intro σ hσ
    refine ⟨universalLaplaceReal Δ_phi σ + 1, ?_⟩
    have h_real_lim := M.tendsto_laplaceSpinReal corr hν hΔ hM hgap hσ
    have h_ev : ∀ᶠ k : ℕ in atTop,
        (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ <
          universalLaplaceReal Δ_phi σ + 1 :=
      h_real_lim.eventually (gt_mem_nhds (by linarith))
    filter_upwards [h_ev] with k hk z hz
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (rpow_nonneg (by positivity) _)]
    have h1 := M.norm_laplaceSpin_le_laplaceSpinReal (2 * (k : ℤ)) z
    have h2 := M.laplaceSpinReal_mono (2 * (k : ℤ)) (lt_trans hz hσ) hσ hz.le
    have h12 : ‖M.laplaceSpin (2 * (k : ℤ)) z‖ ≤ M.laplaceSpinReal (2 * (k : ℤ)) σ :=
      h1.trans h2
    calc
      (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * ‖M.laplaceSpin (2 * (k : ℤ)) z‖
        ≤ (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ :=
          mul_le_mul_of_nonneg_left h12 (rpow_nonneg (by positivity) _)
      _ ≤ universalLaplaceReal Δ_phi σ + 1 := hk.le
  · intro x hx
    rw [universalLaplace_ofReal Δ_phi hx]
    have h_real_lim :=
      (Complex.continuous_ofReal.tendsto _).comp (M.tendsto_laplaceSpinReal corr hν hΔ hM hgap hx)
    refine h_real_lim.congr (fun k => ?_)
    dsimp [Function.comp_def]
    rw [Complex.ofReal_mul, M.laplaceSpin_ofReal]

/-!
## Stage 3: Pairing with $\varphi(h)$ via Vertical Contour Integration and Dominated Convergence
-/

/-- **Dominated Convergence of the Vertical $t$-Integral for $\Delta_\phi > 1/2$ (`sorry`-free)**:
For $\Delta_\phi > 1/2$ and $\sigma < 0$, Lebesgue's Dominated Convergence Theorem yields
convergence of the vertical $t$-integral to the vertical integral against
`universalLaplace Δ_phi` (proved with zero `sorry`s). -/
theorem tendsto_integral_laplaceSpin_of_half_lt {ν Δ_phi h_gap : ℝ}
    (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν) (hΔ : 1 / 2 < Δ_phi)
    (hM : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      M.eval wl wr = corr.correlator_pdisk wl wr)
    (hgap : M.HasTwistGap h_gap)
    {φ : ℝ → ℝ} (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_supp : HasCompactSupport φ)
    {σ : ℝ} (hσ : σ < 0) :
    Tendsto
      (fun k : ℕ =>
        (((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) : ℝ) : ℂ) *
          ((2 * π : ℂ)⁻¹ * ∫ t : ℝ,
            laplaceFourierTransform φ σ t *
              M.laplaceSpin (2 * (k : ℤ)) ((σ : ℂ) + (t : ℂ) * I)))
      atTop
      (𝓝 ((2 * π : ℂ)⁻¹ * ∫ t : ℝ,
        laplaceFourierTransform φ σ t * universalLaplace Δ_phi ((σ : ℂ) + (t : ℂ) * I))) := by
  let F : ℕ → ℝ → ℂ := fun k t =>
    laplaceFourierTransform φ σ t *
      ((((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) : ℝ) : ℂ) *
        M.laplaceSpin (2 * (k : ℤ)) ((σ : ℂ) + (t : ℂ) * I))
  let f : ℝ → ℂ := fun t =>
    laplaceFourierTransform φ σ t * universalLaplace Δ_phi ((σ : ℂ) + (t : ℂ) * I)
  let bound : ℝ → ℝ := fun t =>
    (universalLaplaceReal Δ_phi σ + 1) * ‖laplaceFourierTransform φ σ t‖
  have h_mem : ∀ t : ℝ, (σ : ℂ) + (t : ℂ) * I ∈ UcDisk := by
    intro t
    change ((σ : ℂ) + (t : ℂ) * I).re < 0
    simpa using hσ
  have h_dom : Tendsto (fun k : ℕ => ∫ t : ℝ, F k t) atTop (𝓝 (∫ t : ℝ, f t)) := by
    refine tendsto_integral_filter_of_dominated_convergence bound ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun k => Continuous.aestronglyMeasurable ?_
      have h1 := continuous_laplaceFourierTransform hφ_smooth.continuous hφ_supp σ
      have h2 : Continuous (fun t : ℝ => M.laplaceSpin (2 * (k : ℤ)) ((σ : ℂ) + (t : ℂ) * I)) :=
        (M.differentiableOn_laplaceSpin (2 * (k : ℤ))).continuousOn.comp_continuous
          (by fun_prop) h_mem
      exact h1.mul (continuous_const.mul h2)
    · have h_real_lim := M.tendsto_laplaceSpinReal_of_half_lt corr hν hΔ hM hgap hσ
      have h_ev : ∀ᶠ k : ℕ in atTop,
          (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ <
            universalLaplaceReal Δ_phi σ + 1 :=
        h_real_lim.eventually (gt_mem_nhds (by linarith))
      filter_upwards [h_ev] with k hk
      filter_upwards with t
      dsimp [F, bound]
      rw [norm_mul, mul_comm ‖laplaceFourierTransform φ σ t‖]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact (M.norm_rescaled_laplaceSpin_le Δ_phi k σ t).trans hk.le
    · exact (integrable_laplaceFourierTransform hφ_smooth hφ_supp σ).norm.const_mul _
    · filter_upwards with t
      exact (M.tendsto_laplaceSpin_of_half_lt corr hν hΔ hM hgap (h_mem t)).const_mul
        (laplaceFourierTransform φ σ t)
  have h_mul := h_dom.const_mul (2 * π : ℂ)⁻¹
  refine h_mul.congr (fun k => ?_)
  dsimp [F]
  have h_int_eq :
      (∫ t : ℝ, laplaceFourierTransform φ σ t *
        ((((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) : ℝ) : ℂ) *
          M.laplaceSpin (2 * (k : ℤ)) ((σ : ℂ) + (t : ℂ) * I))) =
      (((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) : ℝ) : ℂ) *
        ∫ t : ℝ, laplaceFourierTransform φ σ t *
          M.laplaceSpin (2 * (k : ℤ)) ((σ : ℂ) + (t : ℂ) * I) := by
    rw [← integral_const_mul]
    congr 1
    ext t
    ring
  rw [h_int_eq]
  ring

/-- **Main Theorem for $\Delta_\phi > 1/2$ (`sorry`-free Monomial Lightcone Bootstrap)**:
In any reflection-positive CFT (`FourPointData ν Δ_phi` with $\nu \ge 0, \Delta_\phi > 1/2$) whose
monomial decomposition `M` has a twist gap $h_{\text{gap}} > 0$, the individual large-spin limit
$J = 2k \to \infty$ of the rescaled spin-$J$ spectral density integrated against any compactly
supported smooth test function $\varphi : \mathbb{R} \to \mathbb{R}$ is universal and given
explicitly by `universalMonomialPairing Δ_phi φ` (proved with zero `sorry`s):
$$\lim_{k \to \infty} (2k)^{1 - 2\Delta_\phi} \int_{\mathbb{R}} \varphi(h) \, d\mu_{2k}(h) =
  \frac{2 \cdot 4^{2\Delta_\phi}}{\Gamma(2\Delta_\phi)}
  \sum_{n=0}^{\infty} \frac{(2\Delta_\phi)_n}{n!} \varphi(\Delta_\phi + n).$$ -/
theorem tendsto_pairSpin_large_even_spin_of_half_lt {ν Δ_phi h_gap : ℝ}
    (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν) (hΔ : 1 / 2 < Δ_phi)
    (hM : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      M.eval wl wr = corr.correlator_pdisk wl wr)
    (hgap : M.HasTwistGap h_gap)
    {φ : ℝ → ℝ} (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_supp : HasCompactSupport φ) :
    Tendsto
      (fun k : ℕ => (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.pairSpin (2 * (k : ℤ)) φ)
      atTop (𝓝 (universalMonomialPairing Δ_phi φ)) := by
  have hΔ_pos : 0 < Δ_phi := by linarith
  have hσ : (-1 : ℝ) < 0 := by norm_num
  have h_int := M.tendsto_integral_laplaceSpin_of_half_lt corr hν hΔ hM hgap hφ_smooth hφ_supp hσ
  rw [integral_laplaceFourierTransform_mul_universalLaplace hΔ_pos hφ_smooth hφ_supp hσ]
    at h_int
  have h_complex : Tendsto
      (fun k : ℕ => (((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.pairSpin (2 * (k : ℤ)) φ : ℝ) : ℂ))
      atTop (𝓝 (universalMonomialPairing Δ_phi φ : ℂ)) := by
    refine h_int.congr' ?_
    filter_upwards with k
    rw [Complex.ofReal_mul,
      M.pairSpin_eq_integral_laplaceSpin (2 * (k : ℤ)) hφ_smooth hφ_supp hσ]
  simpa [Function.comp_def] using (Complex.continuous_re.tendsto _).comp h_complex

/-- **Dominated Convergence of the Vertical $t$-Integral**:
For any $\sigma < 0$, since $(2k)^{1 - 2\Delta_\phi} L_{2k}(\sigma + i t)$ converges pointwise to
`universalLaplace Δ_phi (σ + i t)` (`tendsto_laplaceSpin`) and is bounded uniformly in
$t \in \mathbb{R}$ and $k \in \mathbb{N}$ by the convergent real-axis sequence
$(2k)^{1 - 2\Delta_\phi} L_{2k}(\sigma)$ (`norm_rescaled_laplaceSpin_le` and
`tendsto_laplaceSpinReal`), while `laplaceFourierTransform φ σ` is integrable on $\mathbb{R}$
(`exists_bound_laplaceFourierTransform`), Lebesgue's Dominated Convergence Theorem yields
convergence of the vertical $t$-integral. -/
theorem tendsto_integral_laplaceSpin {ν Δ_phi h_gap : ℝ}
    (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi)
    (hM : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      M.eval wl wr = corr.correlator_pdisk wl wr)
    (hgap : M.HasTwistGap h_gap)
    {φ : ℝ → ℝ} (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_supp : HasCompactSupport φ)
    {σ : ℝ} (hσ : σ < 0) :
    Tendsto
      (fun k : ℕ =>
        (((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) : ℝ) : ℂ) *
          ((2 * π : ℂ)⁻¹ * ∫ t : ℝ,
            laplaceFourierTransform φ σ t *
              M.laplaceSpin (2 * (k : ℤ)) ((σ : ℂ) + (t : ℂ) * I)))
      atTop
      (𝓝 ((2 * π : ℂ)⁻¹ * ∫ t : ℝ,
        laplaceFourierTransform φ σ t * universalLaplace Δ_phi ((σ : ℂ) + (t : ℂ) * I))) := by
  let F : ℕ → ℝ → ℂ := fun k t =>
    laplaceFourierTransform φ σ t *
      ((((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) : ℝ) : ℂ) *
        M.laplaceSpin (2 * (k : ℤ)) ((σ : ℂ) + (t : ℂ) * I))
  let f : ℝ → ℂ := fun t =>
    laplaceFourierTransform φ σ t * universalLaplace Δ_phi ((σ : ℂ) + (t : ℂ) * I)
  let bound : ℝ → ℝ := fun t =>
    (universalLaplaceReal Δ_phi σ + 1) * ‖laplaceFourierTransform φ σ t‖
  have h_mem : ∀ t : ℝ, (σ : ℂ) + (t : ℂ) * I ∈ UcDisk := by
    intro t
    change ((σ : ℂ) + (t : ℂ) * I).re < 0
    simpa using hσ
  have h_dom : Tendsto (fun k : ℕ => ∫ t : ℝ, F k t) atTop (𝓝 (∫ t : ℝ, f t)) := by
    refine tendsto_integral_filter_of_dominated_convergence bound ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun k => Continuous.aestronglyMeasurable ?_
      have h1 := continuous_laplaceFourierTransform hφ_smooth.continuous hφ_supp σ
      have h2 : Continuous (fun t : ℝ => M.laplaceSpin (2 * (k : ℤ)) ((σ : ℂ) + (t : ℂ) * I)) :=
        (M.differentiableOn_laplaceSpin (2 * (k : ℤ))).continuousOn.comp_continuous
          (by fun_prop) h_mem
      exact h1.mul (continuous_const.mul h2)
    · have h_real_lim := M.tendsto_laplaceSpinReal corr hν hΔ hM hgap hσ
      have h_ev : ∀ᶠ k : ℕ in atTop,
          (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.laplaceSpinReal (2 * (k : ℤ)) σ <
            universalLaplaceReal Δ_phi σ + 1 :=
        h_real_lim.eventually (gt_mem_nhds (by linarith))
      filter_upwards [h_ev] with k hk
      filter_upwards with t
      dsimp [F, bound]
      rw [norm_mul, mul_comm ‖laplaceFourierTransform φ σ t‖]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact (M.norm_rescaled_laplaceSpin_le Δ_phi k σ t).trans hk.le
    · exact (integrable_laplaceFourierTransform hφ_smooth hφ_supp σ).norm.const_mul _
    · filter_upwards with t
      exact (M.tendsto_laplaceSpin corr hν hΔ hM hgap (h_mem t)).const_mul
        (laplaceFourierTransform φ σ t)
  have h_mul := h_dom.const_mul (2 * π : ℂ)⁻¹
  refine h_mul.congr (fun k => ?_)
  dsimp [F]
  have h_int_eq :
      (∫ t : ℝ, laplaceFourierTransform φ σ t *
        ((((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) : ℝ) : ℂ) *
          M.laplaceSpin (2 * (k : ℤ)) ((σ : ℂ) + (t : ℂ) * I))) =
      (((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) : ℝ) : ℂ) *
        ∫ t : ℝ, laplaceFourierTransform φ σ t *
          M.laplaceSpin (2 * (k : ℤ)) ((σ : ℂ) + (t : ℂ) * I) := by
    rw [← integral_const_mul]
    congr 1
    ext t
    ring
  rw [h_int_eq]
  ring

/-- **Main Theorem (Monomial Lightcone Bootstrap)**:
In any reflection-positive CFT (`FourPointData ν Δ_phi` with $\nu \ge 0, \Delta_\phi > 0$) whose
monomial decomposition `M` has a twist gap $h_{\text{gap}} > 0$, the individual large-spin limit
$J = 2k \to \infty$ of the rescaled spin-$J$ spectral density integrated against any compactly
supported smooth test function $\varphi : \mathbb{R} \to \mathbb{R}$ is universal:
$$\lim_{k \to \infty} (2k)^{1 - 2\Delta_\phi} \int_{\mathbb{R}} \varphi(h) \, d\mu_{2k}(h) =
  \operatorname{universalMonomialPairing}(\Delta_\phi, \varphi).$$ -/
theorem tendsto_pairSpin_large_even_spin {ν Δ_phi h_gap : ℝ}
    (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi)
    (hM : ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
      M.eval wl wr = corr.correlator_pdisk wl wr)
    (hgap : M.HasTwistGap h_gap)
    {φ : ℝ → ℝ} (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_supp : HasCompactSupport φ) :
    Tendsto
      (fun k : ℕ => (2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.pairSpin (2 * (k : ℤ)) φ)
      atTop (𝓝 (universalMonomialPairing Δ_phi φ)) := by
  have hσ : (-1 : ℝ) < 0 := by norm_num
  have h_int := M.tendsto_integral_laplaceSpin corr hν hΔ hM hgap hφ_smooth hφ_supp hσ
  rw [integral_laplaceFourierTransform_mul_universalLaplace hΔ hφ_smooth hφ_supp hσ]
    at h_int
  have h_complex : Tendsto
      (fun k : ℕ => (((2 * (k : ℝ)) ^ (1 - 2 * Δ_phi) * M.pairSpin (2 * (k : ℤ)) φ : ℝ) : ℂ))
      atTop (𝓝 (universalMonomialPairing Δ_phi φ : ℂ)) := by
    refine h_int.congr' ?_
    filter_upwards with k
    rw [Complex.ofReal_mul,
      M.pairSpin_eq_integral_laplaceSpin (2 * (k : ℤ)) hφ_smooth hφ_supp hσ]
  simpa [Function.comp_def] using (Complex.continuous_re.tendsto _).comp h_complex

end MonomialFourPointData
