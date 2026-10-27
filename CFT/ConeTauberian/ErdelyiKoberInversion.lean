/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Balt van Rees
-/
import CFT.LightconeBootstrap.Transmute1d
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Erdélyi–Kober Fractional Integral and Continuum Primary Spectral Density

This file implements **Phase 1** of `CFT/ConeTauberian/PLAN.md`:
1. **General Real Beta Integral & Change-of-Variable Identities on `Ioo`:
   (`integral_rpow_mul_one_sub_rpow`, `integral_Ioo_aff_sub`, `integral_Ioo_sq_sub`)**:
   We establish the general real Euler Beta integral on `(0, 1)`:
   $$\int_0^1 s^{a - 1} (1 - s)^{b - 1} \, ds = \frac{\Gamma(a)\,\Gamma(b)}{\Gamma(a + b)}
     \qquad (a > 0,\; b > 0),$$
   together with the affine rescaling $s = s' + (1 - s') t$ on `(s', 1)` and the quadratic change
   of variables $s = \xi^2$ ($ds = 2\xi\,d\xi$) on `(\xi', 1)`.
2. **Weyl / Erdélyi–Kober Fractional Integral & Power-Law Eigenfunction Identity
   (`weylIntegralRight`, `weylIntegralRight_one_sub_rpow`)**:
   We define the right-handed Weyl / Erdélyi–Kober fractional integral of order $\nu > 0$ on
   `(0, 1)` and prove its exact action on power laws $(1 - s)^{\alpha - 1}$:
   $$\frac{1}{\Gamma(\nu)} \int_{s'}^1 (s - s')^{\nu - 1} (1 - s)^{\alpha - 1} \, ds
     = \frac{\Gamma(\alpha)}{\Gamma(\alpha + \nu)} (1 - s')^{\alpha + \nu - 1}.$$
3. **Continuum Primary Spectral Density $\rho^{\text{prim}}_{\nu, \Delta_\phi}(u, \xi)$ and Exact
   $d \to 2$ Branching & Cylinder Integrals
   (`primaryConeDensity`, `primaryConeDensity_eq_weylIntegralRight`,
   `integral_branchingKernel_mul_primaryConeDensity`, `integral_primaryConeDensity_cylinder`)**:
   We define the continuum primary spectral density $\rho^{\text{prim}}_{\nu, \Delta_\phi}(u, \xi)$,
   prove that it equals the closed-form evaluation of the complementary Weyl fractional integral
   $I_-^{1-\nu}$ applied to $-\frac{d}{ds}(1 - s)^{2\Delta_\phi - 3/2}$, define the 2D effective
   density $\rho_{2d}^{\text{eff}}(\Delta_\phi, u, \xi')$ and the cumulative primary constant
   $\mathcal{C}^{\text{prim}}_\nu(\Delta_\phi)$, and prove both:
   - the exact Erdélyi–Kober branching identity mapping $\rho^{\text{prim}}_{\nu, \Delta_\phi}$
     onto $\rho_{2d}^{\text{eff}}$, and
   - the full cylinder integral $\int_0^1 \int_0^1 \rho^{\text{prim}}_{\nu, \Delta_\phi}(u, \xi)
     \, d\xi \, du = \mathcal{C}^{\text{prim}}_\nu(\Delta_\phi)$.
4. **Monotone Sandwiching Lemma (`tendsto_of_le_of_ge_approx`)**:
   A general filter convergence lemma deducing $\lim_{\Delta \to \infty} F(\Delta) = L$ whenever
   $F(\Delta)$ can be sandwiched within $\varepsilon$ of $L$ by smooth approximations.
-/

open MeasureTheory Set Filter Metric Real Complex Topology
open scoped BigOperators ENNReal

namespace CFT.ConeTauberian

/-! ## Section 1: General Real Beta Integral & Change of Variables on `Ioo` -/

/-- Real-to-complex power identity for the Beta integrand $s^{a - 1} (1 - s)^{b - 1}$ on
`Ioo (0 : ℝ) 1`. -/
lemma ofReal_rpow_mul_one_sub_rpow (a b : ℝ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    ((s ^ (a - 1) * (1 - s) ^ (b - 1) : ℝ) : ℂ) =
      (s : ℂ) ^ ((a : ℂ) - 1) * (1 - (s : ℂ)) ^ ((b : ℂ) - 1) := by
  have hs1 : 0 ≤ 1 - s := (sub_pos.mpr hs.2).le
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hs.1.le, Complex.ofReal_cpow hs1]
  congr 1 <;> congr 1 <;> push_cast <;> ring

/-- **Real Euler Beta Integral on `Ioo (0 : ℝ) 1`**:
for all $a > 0$ and $b > 0$,
$$\int_0^1 s^{a - 1} (1 - s)^{b - 1} \, ds = \frac{\Gamma(a)\,\Gamma(b)}{\Gamma(a + b)}.$$ -/
theorem integral_rpow_mul_one_sub_rpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ s in Ioo (0 : ℝ) 1, s ^ (a - 1) * (1 - s) ^ (b - 1)) =
      Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  set u : ℂ := (a : ℂ)
  set v : ℂ := (b : ℂ)
  have hu : 0 < u.re := by simp [u, ha]
  have hv : 0 < v.re := by simp [v, hb]
  have h_c : (((∫ s in Ioo (0 : ℝ) 1, s ^ (a - 1) * (1 - s) ^ (b - 1)) : ℝ) : ℂ) =
      Complex.betaIntegral u v := by
    rw [← integral_complex_ofReal]
    have h_congr :
        (∫ s in Ioo (0 : ℝ) 1, ((s ^ (a - 1) * (1 - s) ^ (b - 1) : ℝ) : ℂ)) =
          ∫ s in Ioo (0 : ℝ) 1, (s : ℂ) ^ (u - 1) * (1 - (s : ℂ)) ^ (v - 1) :=
      setIntegral_congr_fun measurableSet_Ioo fun s hs => by
        simpa [u, v] using ofReal_rpow_mul_one_sub_rpow a b hs
    rw [h_congr, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_one]
    rfl
  rw [Complex.betaIntegral_eq_Gamma_mul_div u v hu hv] at h_c
  have huv_eq : u + v = ((a + b : ℝ) : ℂ) := by dsimp [u, v]; push_cast; ring
  rw [huv_eq, Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal] at h_c
  exact_mod_cast h_c

/-- Power-law integral on `Ioo (0 : ℝ) 1`: for $a > 0$, $\int_0^1 u^{a - 1} \, du = a⁻¹$. -/
theorem integral_rpow_Ioo_zero_one {a : ℝ} (ha : 0 < a) :
    (∫ u in Ioo (0 : ℝ) 1, u ^ (a - 1)) = a⁻¹ := by
  have h := integral_rpow_mul_one_sub_rpow ha zero_lt_one
  have h_congr :
      (∫ s in Ioo (0 : ℝ) 1, s ^ (a - 1) * (1 - s) ^ ((1 : ℝ) - 1)) =
        ∫ s in Ioo (0 : ℝ) 1, s ^ (a - 1) := by
    refine setIntegral_congr_fun measurableSet_Ioo fun s _ => ?_
    simp
  rw [h_congr, Real.Gamma_one, mul_one, Real.Gamma_add_one ha.ne'] at h
  rw [h]
  have hG : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  field_simp

/-- Image of `Ioo (0 : ℝ) 1` under the affine map $t \mapsto s' + (1 - s') t$ for $s' < 1$. -/
lemma image_affine_Ioo {s' : ℝ} (hs' : s' < 1) :
    (fun t : ℝ => s' + (1 - s') * t) '' Ioo (0 : ℝ) 1 = Ioo s' 1 := by
  have h1 : 0 < 1 - s' := sub_pos.mpr hs'
  ext s
  simp only [mem_image, mem_Ioo]
  constructor
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    refine ⟨by nlinarith, by nlinarith⟩
  · rintro ⟨hs0, hs1⟩
    refine ⟨(s - s') / (1 - s'), ⟨div_pos (sub_pos.mpr hs0) h1, ?_⟩, ?_⟩
    · rw [div_lt_one h1]
      linarith
    · field_simp
      ring

/-- Affine change of variables $s = s' + (1 - s') t$ on `Ioo s' 1` for $s' < 1$. -/
theorem integral_Ioo_affine_sub {s' : ℝ} (hs' : s' < 1) (f : ℝ → ℝ) :
    (∫ s in Ioo s' 1, f s) =
      ∫ t in Ioo (0 : ℝ) 1, (1 - s') * f (s' + (1 - s') * t) := by
  have h1 : 0 < 1 - s' := sub_pos.mpr hs'
  rw [← image_affine_Ioo hs']
  have hinj : InjOn (fun t : ℝ => s' + (1 - s') * t) (Ioo (0 : ℝ) 1) := by
    intro x _ y _ hxy
    have : (1 - s') * x = (1 - s') * y := by linarith
    exact mul_left_cancel₀ h1.ne' this
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivWithinAt (fun x : ℝ => s' + (1 - s') * x) (1 - s') (Ioo (0 : ℝ) 1) t := by
    intro t _
    have hd : HasDerivAt (fun x : ℝ => s' + (1 - s') * x) (1 - s') t := by
      simpa using ((hasDerivAt_id t).const_mul (1 - s')).const_add s'
    exact hd.hasDerivWithinAt
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj]
  refine setIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
  simp [abs_of_pos h1, smul_eq_mul]

/-- Image of `Ioo ξ' 1` under the squaring map $\xi \mapsto \xi^2$ for $0 \le \xi'$. -/
lemma image_sq_Ioo {ξ' : ℝ} (hξ'0 : 0 ≤ ξ') :
    (fun ξ : ℝ => ξ ^ 2) '' Ioo ξ' 1 = Ioo (ξ' ^ 2) 1 := by
  ext s
  simp only [mem_image, mem_Ioo]
  constructor
  · rintro ⟨ξ, ⟨h1, h2⟩, rfl⟩
    have hξ0 : 0 < ξ := lt_of_le_of_lt hξ'0 h1
    refine ⟨?_, ?_⟩
    · nlinarith
    · nlinarith
  · rintro ⟨hs0, hs1⟩
    have hs_pos : 0 < s := lt_of_le_of_lt (sq_nonneg ξ') hs0
    refine ⟨Real.sqrt s, ⟨?_, ?_⟩, Real.sq_sqrt hs_pos.le⟩
    · rw [← Real.sqrt_sq hξ'0]
      exact Real.sqrt_lt_sqrt (sq_nonneg ξ') hs0
    · rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt hs_pos.le hs1

/-- Quadratic change of variables $s = \xi^2$ ($ds = 2\xi\,d\xi$) on `Ioo ξ' 1` for
$0 \le \xi'$. -/
theorem integral_Ioo_sq_sub {ξ' : ℝ} (hξ'0 : 0 ≤ ξ') (f : ℝ → ℝ) :
    (∫ s in Ioo (ξ' ^ 2) 1, f s) =
      ∫ ξ in Ioo ξ' 1, (2 * ξ) * f (ξ ^ 2) := by
  rw [← image_sq_Ioo hξ'0]
  have hinj : InjOn (fun ξ : ℝ => ξ ^ 2) (Ioo ξ' 1) := by
    intro x hx y hy hxy
    have hx0 : 0 < x := lt_of_le_of_lt hξ'0 hx.1
    have hy0 : 0 < y := lt_of_le_of_lt hξ'0 hy.1
    nlinarith
  have hderiv : ∀ ξ ∈ Ioo ξ' 1,
      HasDerivWithinAt (fun x : ℝ => x ^ 2) (2 * ξ) (Ioo ξ' 1) ξ := by
    intro ξ _
    have hd : HasDerivAt (fun x : ℝ => x ^ 2) (2 * ξ) ξ := by
      simpa using hasDerivAt_pow 2 ξ
    exact hd.hasDerivWithinAt
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj]
  refine setIntegral_congr_fun measurableSet_Ioo fun ξ hξ => ?_
  have hξ0 : 0 < 2 * ξ := by linarith [lt_of_le_of_lt hξ'0 hξ.1]
  simp [abs_of_pos hξ0, smul_eq_mul]

/-! ## Section 2: Weyl / Erdélyi–Kober Fractional Integral & Power-Law Eigenfunction Identity -/

/-- The right-handed Weyl / Erdélyi–Kober fractional integral of order $\nu > 0$ on `(0, 1)`:
$$(I_-^\nu g)(s') := \frac{1}{\Gamma(\nu)} \int_{s'}^1 (s - s')^{\nu - 1} g(s) \, ds.$$ -/
noncomputable def weylIntegralRight (ν : ℝ) (g : ℝ → ℝ) (s' : ℝ) : ℝ :=
  (Real.Gamma ν)⁻¹ * ∫ s in Ioo s' 1, (s - s') ^ (ν - 1) * g s

/-- **Fundamental Weyl / Erdélyi–Kober Eigenfunction Identity**:
for $\nu > 0$, $\alpha > 0$, and $s' < 1$,
$$\frac{1}{\Gamma(\nu)} \int_{s'}^1 (s - s')^{\nu - 1} (1 - s)^{\alpha - 1} \, ds
  = \frac{\Gamma(\alpha)}{\Gamma(\alpha + \nu)} (1 - s')^{\alpha + \nu - 1}.$$ -/
theorem weylIntegralRight_one_sub_rpow {ν α s' : ℝ} (hν : 0 < ν) (hα : 0 < α)
    (hs' : s' < 1) :
    weylIntegralRight ν (fun s => (1 - s) ^ (α - 1)) s' =
      (Real.Gamma α / Real.Gamma (α + ν)) * (1 - s') ^ (α + ν - 1) := by
  have h1 : 0 < 1 - s' := sub_pos.mpr hs'
  dsimp [weylIntegralRight]
  rw [integral_Ioo_affine_sub hs']
  have h_congr :
      (∫ t in Ioo (0 : ℝ) 1,
        (1 - s') *
          ((s' + (1 - s') * t - s') ^ (ν - 1) * (1 - (s' + (1 - s') * t)) ^ (α - 1))) =
      (1 - s') ^ (α + ν - 1) *
        ∫ t in Ioo (0 : ℝ) 1, t ^ (ν - 1) * (1 - t) ^ (α - 1) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    have ht0 : 0 < t := ht.1
    have ht1 : 0 < 1 - t := sub_pos.mpr ht.2
    have h_diff1 : s' + (1 - s') * t - s' = (1 - s') * t := by ring
    have h_diff2 : 1 - (s' + (1 - s') * t) = (1 - s') * (1 - t) := by ring
    rw [h_diff1, h_diff2,
      Real.mul_rpow h1.le ht0.le,
      Real.mul_rpow h1.le ht1.le]
    have h_pow :
        (1 - s') * (1 - s') ^ (ν - 1) * (1 - s') ^ (α - 1) = (1 - s') ^ (α + ν - 1) := by
      have h_base : (1 - s') * (1 - s') ^ (ν - 1) = (1 - s') ^ ((1 : ℝ) + (ν - 1)) := by
        rw [Real.rpow_add h1, Real.rpow_one]
      rw [h_base, ← Real.rpow_add h1]
      congr 1
      ring
    calc
      (1 - s') * (((1 - s') ^ (ν - 1) * t ^ (ν - 1)) *
          ((1 - s') ^ (α - 1) * (1 - t) ^ (α - 1)))
        = ((1 - s') * (1 - s') ^ (ν - 1) * (1 - s') ^ (α - 1)) *
            (t ^ (ν - 1) * (1 - t) ^ (α - 1)) := by ring
      _ = (1 - s') ^ (α + ν - 1) * (t ^ (ν - 1) * (1 - t) ^ (α - 1)) := by rw [h_pow]
  rw [h_congr, integral_rpow_mul_one_sub_rpow hν hα]
  have hGν : Real.Gamma ν ≠ 0 := (Real.Gamma_pos_of_pos hν).ne'
  have h_add : ν + α = α + ν := add_comm ν α
  rw [h_add]
  field_simp

/-! ## Section 3: Continuum Primary Spectral Density & Exact Branching and Cylinder Integrals -/

/-- The normalization constant $c_{\nu, \Delta_\phi} > 0$ of the continuum primary spectral density:
$$c_{\nu, \Delta_\phi} :=
  \frac{2^{2\nu + 1} \, \Gamma(\nu) \, \Gamma(2\Delta_\phi - 1/2)}
       {\Gamma(\Delta_\phi)^4 \, \Gamma(2\Delta_\phi - \nu - 1/2)}.$$ -/
noncomputable def primaryConeConst (ν Δ_phi : ℝ) : ℝ :=
  (2 : ℝ) ^ (2 * ν + 1) * Real.Gamma ν * Real.Gamma (2 * Δ_phi - 1 / 2) /
    ((Real.Gamma Δ_phi) ^ 4 * Real.Gamma (2 * Δ_phi - ν - 1 / 2))

/-- The continuum primary spectral density on $(u, \xi) \in (0, \infty) \times (0, 1)$:
$$\rho^{\text{prim}}_{\nu, \Delta_\phi}(u, \xi) :=
  c_{\nu, \Delta_\phi} \, u^{4\Delta_\phi - 2\nu - 1} \,
  \xi^{2\nu} \left(1 - \xi^2\right)^{2\Delta_\phi - \nu - 3/2}.$$ -/
noncomputable def primaryConeDensity (ν Δ_phi u ξ : ℝ) : ℝ :=
  primaryConeConst ν Δ_phi * u ^ (4 * Δ_phi - 2 * ν - 1) *
    ξ ^ (2 * ν) * (1 - ξ ^ 2) ^ (2 * Δ_phi - ν - 3 / 2)

/-- **Closed-Form Algebraic Evaluation of the Erdélyi–Kober Inversion Integral**:
for $\nu < 1$, $\Delta_\phi > 3/4$, and $\xi \in (-1, 1)$, applying the complementary
Weyl fractional integral $I_-^{1 - \nu}$ to $-\frac{d}{ds}(1 - s)^{2\Delta_\phi - 3/2}
= (2\Delta_\phi - 3/2)(1 - s)^{2\Delta_\phi - 5/2}$ at $s' = \xi^2$ evaluates in closed algebraic
form to `primaryConeDensity ν Δ_phi u ξ`. -/
theorem primaryConeDensity_eq_weylIntegralRight {ν Δ_phi u ξ : ℝ}
    (hν1 : ν < 1) (hΔ : 3 / 4 < Δ_phi) (hξ : ξ ^ 2 < 1) :
    ((2 : ℝ) ^ (2 * ν + 1) * Real.Gamma ν * (2 * Δ_phi - 3 / 2) / (Real.Gamma Δ_phi) ^ 4) *
      u ^ (4 * Δ_phi - 2 * ν - 1) * ξ ^ (2 * ν) *
      weylIntegralRight (1 - ν) (fun s => (1 - s) ^ ((2 * Δ_phi - 3 / 2) - 1)) (ξ ^ 2) =
    primaryConeDensity ν Δ_phi u ξ := by
  have h1ν : 0 < 1 - ν := sub_pos.mpr hν1
  have hα : 0 < 2 * Δ_phi - 3 / 2 := by linarith
  rw [weylIntegralRight_one_sub_rpow h1ν hα hξ]
  dsimp [primaryConeDensity, primaryConeConst]
  have h_add1 : 2 * Δ_phi - 3 / 2 + (1 - ν) = 2 * Δ_phi - ν - 1 / 2 := by ring
  have h_add2 : (2 * Δ_phi - ν - 1 / 2) - 1 = 2 * Δ_phi - ν - 3 / 2 := by ring
  have h_gamma : (2 * Δ_phi - 3 / 2) * Real.Gamma (2 * Δ_phi - 3 / 2) =
      Real.Gamma (2 * Δ_phi - 1 / 2) := by
    have h_step : 2 * Δ_phi - 1 / 2 = (2 * Δ_phi - 3 / 2) + 1 := by ring
    rw [h_step, Real.Gamma_add_one hα.ne']
  rw [h_add1, h_add2, ← h_gamma]
  ring

/-- The 2D effective continuum density on $(u, \xi') \in (0, \infty) \times (0, 1)$:
$$\rho_{2d}^{\text{eff}}(\Delta_\phi, u, \xi') :=
  \frac{4}{\Gamma(\Delta_\phi)^4} \, u^{4\Delta_\phi - 2}
  \left(1 - (\xi')^2\right)^{2\Delta_\phi - 3/2}.$$ -/
noncomputable def eff2dDensity (Δ_phi u ξ' : ℝ) : ℝ :=
  (4 / (Real.Gamma Δ_phi) ^ 4) * u ^ (4 * Δ_phi - 2) *
    (1 - ξ' ^ 2) ^ (2 * Δ_phi - 3 / 2)

/-- The cumulative unweighted primary OPE constant:
$$\mathcal{C}^{\text{prim}}_\nu(\Delta_\phi) :=
  \frac{2^{2\nu - 1} \, \Gamma(\nu) \, \Gamma(\nu + 1/2) \, \Gamma(2\Delta_\phi - 1/2)}
       {(2\Delta_\phi - \nu) \, \Gamma(\Delta_\phi)^4 \, \Gamma(2\Delta_\phi)}.$$ -/
noncomputable def cumulativePrimaryConst (ν Δ_phi : ℝ) : ℝ :=
  (2 : ℝ) ^ (2 * ν - 1) * Real.Gamma ν * Real.Gamma (ν + 1 / 2) *
    Real.Gamma (2 * Δ_phi - 1 / 2) /
    ((2 * Δ_phi - ν) * (Real.Gamma Δ_phi) ^ 4 * Real.Gamma (2 * Δ_phi))

/-- The continuum $d \to 2$ Erdélyi–Kober branching kernel
$$\mathcal{K}_\nu(\xi, \xi') :=
  \frac{2^{2 - 2\nu}}{\Gamma(\nu)^2} \, \xi^{1 - 2\nu}
  \left(\xi^2 - (\xi')^2\right)^{\nu - 1} \mathbf{1}_{\xi' < \xi}.$$ -/
noncomputable def branchingKernel (ν ξ ξ' : ℝ) : ℝ :=
  if ξ' < ξ then
    (2 : ℝ) ^ (2 - 2 * ν) / (Real.Gamma ν) ^ 2 *
      ξ ^ (1 - 2 * ν) * (ξ ^ 2 - ξ' ^ 2) ^ (ν - 1)
  else 0

/-- **Exact Erdélyi–Kober Branching Identity for `primaryConeDensity`**:
integrating $\rho^{\text{prim}}_{\nu, \Delta_\phi}(u, \xi)$ against the continuum $d \to 2$
branching kernel $u^{2\nu - 1} \mathcal{K}_\nu(\xi, \xi')$ over $\xi \in (\xi', 1)$ reproduces the
2D effective density $\rho_{2d}^{\text{eff}}(\Delta_\phi, u, \xi')$. -/
theorem integral_branchingKernel_mul_primaryConeDensity {ν Δ_phi u ξ' : ℝ}
    (hν : 0 < ν) (hΔ : ν / 2 + 1 / 4 < Δ_phi) (hu : 0 < u)
    (hξ'0 : 0 ≤ ξ') (hξ'1 : ξ' < 1) :
    (∫ ξ in Ioo ξ' 1,
      u ^ (2 * ν - 1) * branchingKernel ν ξ ξ' * primaryConeDensity ν Δ_phi u ξ) =
      eff2dDensity Δ_phi u ξ' := by
  have hs'1 : ξ' ^ 2 < 1 := by nlinarith
  have hα : 0 < 2 * Δ_phi - ν - 1 / 2 := by linarith
  have h_congr :
      (∫ ξ in Ioo ξ' 1,
        u ^ (2 * ν - 1) * branchingKernel ν ξ ξ' * primaryConeDensity ν Δ_phi u ξ) =
      (u ^ (4 * Δ_phi - 2) * (2 : ℝ) ^ (1 - 2 * ν) / Real.Gamma ν * primaryConeConst ν Δ_phi) *
        ((Real.Gamma ν)⁻¹ *
          ∫ ξ in Ioo ξ' 1,
            (2 * ξ) * ((ξ ^ 2 - ξ' ^ 2) ^ (ν - 1) *
              (1 - ξ ^ 2) ^ ((2 * Δ_phi - ν - 1 / 2) - 1))) := by
    rw [← integral_const_mul, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun ξ hξ => ?_
    have hξ_pos : 0 < ξ := lt_of_le_of_lt hξ'0 hξ.1
    simp only [branchingKernel, hξ.1, ↓reduceIte, primaryConeDensity]
    have hu_pow : u ^ (2 * ν - 1) * u ^ (4 * Δ_phi - 2 * ν - 1) = u ^ (4 * Δ_phi - 2) := by
      rw [← Real.rpow_add hu]
      congr 1; ring
    have hξ_pow : ξ ^ (1 - 2 * ν) * ξ ^ (2 * ν) = ξ := by
      rw [← Real.rpow_add hξ_pos]
      have : (1 - 2 * ν) + 2 * ν = (1 : ℝ) := by ring
      rw [this, Real.rpow_one]
    have h2_pow : (2 : ℝ) ^ (2 - 2 * ν) = 2 * (2 : ℝ) ^ (1 - 2 * ν) := by
      have : (2 : ℝ) ^ (2 - 2 * ν) = (2 : ℝ) ^ ((1 : ℝ) + (1 - 2 * ν)) := by
        congr 1; ring
      rw [this, Real.rpow_add two_pos, Real.rpow_one]
    have h1_exp : 2 * Δ_phi - ν - 3 / 2 = (2 * Δ_phi - ν - 1 / 2) - 1 := by ring
    rw [h2_pow, h1_exp]
    calc
      u ^ (2 * ν - 1) *
          (2 * (2 : ℝ) ^ (1 - 2 * ν) / (Real.Gamma ν) ^ 2 *
            ξ ^ (1 - 2 * ν) * (ξ ^ 2 - ξ' ^ 2) ^ (ν - 1)) *
          (primaryConeConst ν Δ_phi * u ^ (4 * Δ_phi - 2 * ν - 1) *
            ξ ^ (2 * ν) * (1 - ξ ^ 2) ^ (2 * Δ_phi - ν - 1 / 2 - 1))
        = (u ^ (2 * ν - 1) * u ^ (4 * Δ_phi - 2 * ν - 1)) *
            (ξ ^ (1 - 2 * ν) * ξ ^ (2 * ν)) *
            (2 * (2 : ℝ) ^ (1 - 2 * ν) / (Real.Gamma ν) ^ 2 * primaryConeConst ν Δ_phi *
              ((ξ ^ 2 - ξ' ^ 2) ^ (ν - 1) *
                (1 - ξ ^ 2) ^ (2 * Δ_phi - ν - 1 / 2 - 1))) := by ring
      _ = u ^ (4 * Δ_phi - 2) * ξ *
            (2 * (2 : ℝ) ^ (1 - 2 * ν) / (Real.Gamma ν) ^ 2 * primaryConeConst ν Δ_phi *
              ((ξ ^ 2 - ξ' ^ 2) ^ (ν - 1) *
                (1 - ξ ^ 2) ^ (2 * Δ_phi - ν - 1 / 2 - 1))) := by
          rw [hu_pow, hξ_pow]
      _ = u ^ (4 * Δ_phi - 2) * (2 : ℝ) ^ (1 - 2 * ν) / Real.Gamma ν *
            primaryConeConst ν Δ_phi *
            ((Real.Gamma ν)⁻¹ *
              (2 * ξ * ((ξ ^ 2 - ξ' ^ 2) ^ (ν - 1) *
                (1 - ξ ^ 2) ^ (2 * Δ_phi - ν - 1 / 2 - 1)))) := by
          ring
  rw [h_congr, ← integral_Ioo_sq_sub hξ'0
    (fun s => (s - ξ' ^ 2) ^ (ν - 1) * (1 - s) ^ ((2 * Δ_phi - ν - 1 / 2) - 1))]
  change (u ^ (4 * Δ_phi - 2) * (2 : ℝ) ^ (1 - 2 * ν) / Real.Gamma ν *
      primaryConeConst ν Δ_phi) *
    weylIntegralRight ν (fun s => (1 - s) ^ ((2 * Δ_phi - ν - 1 / 2) - 1)) (ξ' ^ 2) = _
  rw [weylIntegralRight_one_sub_rpow hν hα hs'1]
  dsimp [primaryConeConst, eff2dDensity]
  have hΔ_pos : 0 < Δ_phi := by linarith
  have hGν : Real.Gamma ν ≠ 0 := (Real.Gamma_pos_of_pos hν).ne'
  have hGΔ : Real.Gamma Δ_phi ≠ 0 := (Real.Gamma_pos_of_pos hΔ_pos).ne'
  have hG1 : Real.Gamma (2 * Δ_phi - 1 / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hG2 : Real.Gamma (2 * Δ_phi - ν - 1 / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  have h_add1 : 2 * Δ_phi - ν - 1 / 2 + ν = 2 * Δ_phi - 1 / 2 := by ring
  have h_add2 : (2 * Δ_phi - 1 / 2) - 1 = 2 * Δ_phi - 3 / 2 := by ring
  have h2_mul : (2 : ℝ) ^ (1 - 2 * ν) * (2 : ℝ) ^ (2 * ν + 1) = 4 := by
    rw [← Real.rpow_add two_pos]
    have : (1 - 2 * ν) + (2 * ν + 1) = (2 : ℝ) := by ring
    rw [this]
    norm_num
  rw [h_add1, h_add2]
  set g1 := Real.Gamma (2 * Δ_phi - 1 / 2)
  set g2 := Real.Gamma (2 * Δ_phi - ν - 1 / 2)
  set gν := Real.Gamma ν
  set gΔ := Real.Gamma Δ_phi
  field_simp
  linear_combination h2_mul

/-- Angular integral of `primaryConeDensity` over $\xi \in (0, 1)$ for fixed $u > 0$. -/
theorem integral_primaryConeDensity_xi {ν Δ_phi u : ℝ}
    (hν : 0 < ν) (hΔ : ν / 2 + 1 / 4 < Δ_phi) :
    (∫ ξ in Ioo (0 : ℝ) 1, primaryConeDensity ν Δ_phi u ξ) =
      (2 * (2 * Δ_phi - ν)) * cumulativePrimaryConst ν Δ_phi *
        u ^ (4 * Δ_phi - 2 * ν - 1) := by
  have h_congr :
      (∫ ξ in Ioo (0 : ℝ) 1, primaryConeDensity ν Δ_phi u ξ) =
        (primaryConeConst ν Δ_phi * u ^ (4 * Δ_phi - 2 * ν - 1) / 2) *
          ∫ ξ in Ioo (0 : ℝ) 1,
            (2 * ξ) * ((ξ ^ 2) ^ ((ν + 1 / 2) - 1) *
              (1 - ξ ^ 2) ^ ((2 * Δ_phi - ν - 1 / 2) - 1)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun ξ hξ => ?_
    have hξ0 : 0 < ξ := hξ.1
    dsimp [primaryConeDensity]
    have h_sq_pow : (ξ ^ 2) ^ ((ν + 1 / 2) - 1) = ξ ^ (2 * ν - 1) := by
      rw [← Real.rpow_natCast ξ 2, ← Real.rpow_mul hξ0.le]
      congr 1; ring
    have h_xi_mul : ξ * ξ ^ (2 * ν - 1) = ξ ^ (2 * ν) := by
      have : ξ * ξ ^ (2 * ν - 1) = ξ ^ ((1 : ℝ) + (2 * ν - 1)) := by
        rw [Real.rpow_add hξ0, Real.rpow_one]
      rw [this]
      congr 1; ring
    have h_exp : (2 * Δ_phi - ν - 1 / 2) - 1 = 2 * Δ_phi - ν - 3 / 2 := by ring
    rw [h_sq_pow, h_exp]
    calc
      primaryConeConst ν Δ_phi * u ^ (4 * Δ_phi - 2 * ν - 1) *
          ξ ^ (2 * ν) * (1 - ξ ^ 2) ^ (2 * Δ_phi - ν - 3 / 2)
        = primaryConeConst ν Δ_phi * u ^ (4 * Δ_phi - 2 * ν - 1) *
            (ξ * ξ ^ (2 * ν - 1)) * (1 - ξ ^ 2) ^ (2 * Δ_phi - ν - 3 / 2) := by
          rw [h_xi_mul]
      _ = primaryConeConst ν Δ_phi * u ^ (4 * Δ_phi - 2 * ν - 1) / 2 *
            (2 * ξ * (ξ ^ (2 * ν - 1) * (1 - ξ ^ 2) ^ (2 * Δ_phi - ν - 3 / 2))) := by
          ring
  have h_sq := integral_Ioo_sq_sub (le_refl (0 : ℝ))
    (fun s => s ^ ((ν + 1 / 2) - 1) * (1 - s) ^ ((2 * Δ_phi - ν - 1 / 2) - 1))
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h_sq
  rw [h_congr, ← h_sq,
    integral_rpow_mul_one_sub_rpow (by linarith : 0 < ν + 1 / 2)
      (by linarith : 0 < 2 * Δ_phi - ν - 1 / 2)]
  dsimp [primaryConeConst, cumulativePrimaryConst]
  have hΔ_pos : 0 < Δ_phi := by linarith
  have hGν : Real.Gamma ν ≠ 0 := (Real.Gamma_pos_of_pos hν).ne'
  have hGΔ : Real.Gamma Δ_phi ≠ 0 := (Real.Gamma_pos_of_pos hΔ_pos).ne'
  have hG2 : Real.Gamma (2 * Δ_phi - ν - 1 / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hG2Δ : Real.Gamma (2 * Δ_phi) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  have h_denom : 2 * Δ_phi - ν ≠ 0 := by linarith
  have h_add : ν + 1 / 2 + (2 * Δ_phi - ν - 1 / 2) = 2 * Δ_phi := by ring
  have h2_pow : (2 : ℝ) ^ (2 * ν + 1) = 4 * (2 : ℝ) ^ (2 * ν - 1) := by
    have : (2 : ℝ) ^ (2 * ν + 1) = (2 : ℝ) ^ ((2 : ℝ) + (2 * ν - 1)) := by
      congr 1; ring
    rw [this, Real.rpow_add two_pos]
    norm_num
  rw [h_add, h2_pow]
  set g1 := Real.Gamma (2 * Δ_phi - 1 / 2)
  set g2 := Real.Gamma (2 * Δ_phi - ν - 1 / 2)
  set g3 := Real.Gamma (ν + 1 / 2)
  set g4 := Real.Gamma (2 * Δ_phi)
  set gν := Real.Gamma ν
  set gΔ := Real.Gamma Δ_phi
  field_simp
  ring

/-- **Full Cylinder Integral of `primaryConeDensity` (`PLAN.md`, Corollary 2)**:
for $\nu > 0$ and $\Delta_\phi > \frac{\nu}{2} + \frac{1}{4}$,
$$\int_0^1 \left(\int_0^1 \rho^{\text{prim}}_{\nu, \Delta_\phi}(u, \xi) \, d\xi\right) du
  = \mathcal{C}^{\text{prim}}_\nu(\Delta_\phi).$$ -/
theorem integral_primaryConeDensity_cylinder {ν Δ_phi : ℝ}
    (hν : 0 < ν) (hΔ : ν / 2 + 1 / 4 < Δ_phi) :
    (∫ u in Ioo (0 : ℝ) 1, ∫ ξ in Ioo (0 : ℝ) 1, primaryConeDensity ν Δ_phi u ξ) =
      cumulativePrimaryConst ν Δ_phi := by
  simp_rw [integral_primaryConeDensity_xi hν hΔ]
  rw [integral_const_mul]
  have ha : 0 < 4 * Δ_phi - 2 * ν := by linarith
  have h_u := integral_rpow_Ioo_zero_one ha
  have h_exp : 4 * Δ_phi - 2 * ν - 1 = (4 * Δ_phi - 2 * ν) - 1 := rfl
  rw [h_exp, h_u]
  have h_ne : 2 * Δ_phi - ν ≠ 0 := by linarith
  have h_eq : 4 * Δ_phi - 2 * ν = 2 * (2 * Δ_phi - ν) := by ring
  rw [h_eq]
  field_simp

/-! ## Section 4: Monotone Sandwiching Lemma for Cumulative Asymptotics -/

/-- **Monotone Sandwiching Lemma**:
if $F(\Delta)$ can be sandwiched between approximating quantities $F_-(\Delta) \le F(\Delta) \le
F_+(\Delta)$ whose limits $L_-, L_+$ lie within $\varepsilon$ of $L$ for every $\varepsilon > 0$,
then $\lim_{\Delta \to \infty} F(\Delta) = L$. -/
theorem tendsto_of_le_of_ge_approx {F : ℝ → ℝ} {L : ℝ}
    (h_approx : ∀ ε > 0, ∃ F_minus F_plus : ℝ → ℝ, ∃ L_minus L_plus : ℝ,
      (∀ᶠ Δ in atTop, F_minus Δ ≤ F Δ ∧ F Δ ≤ F_plus Δ) ∧
      Tendsto F_minus atTop (𝓝 L_minus) ∧
      Tendsto F_plus atTop (𝓝 L_plus) ∧
      L - ε ≤ L_minus ∧ L_plus ≤ L + ε) :
    Tendsto F atTop (𝓝 L) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨F_minus, F_plus, L_minus, L_plus, h_sand, h_lim_m, h_lim_p, hLm, hLp⟩ :=
    h_approx (ε / 2) (half_pos hε)
  have hm_ev : ∀ᶠ Δ in atTop, L_minus - ε / 2 < F_minus Δ :=
    h_lim_m.eventually (eventually_gt_nhds (by linarith))
  have hp_ev : ∀ᶠ Δ in atTop, F_plus Δ < L_plus + ε / 2 :=
    h_lim_p.eventually (eventually_lt_nhds (by linarith))
  filter_upwards [h_sand, hm_ev, hp_ev] with Δ ⟨h1, h2⟩ hm hp
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith, by linarith⟩

end CFT.ConeTauberian
