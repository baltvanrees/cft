/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI-generated, edited by Balt van Rees
-/
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import CFT.Corr_pdisk

/-!
# Monomial Decomposition of Four-Point Correlators on `UcPdisk`

This file defines the monomial expansion of a four-point correlation function on the universal cover
of the punctured polydisk $\operatorname{UcPdisk} = \{\operatorname{Re}(w_l) < 0,
\operatorname{Re}(w_r) < 0\}$:
$$\mathcal{G}_{\text{mon}}(w_l, w_r) =
  \sum_{J \in \mathbb{Z}} \int_{\mathbb{R}} e^{h w_l + (h + J) w_r} \, d\mu_J(h),$$
where $\mu_J$ is the non-negative spectral measure at spin $J = \bar{h} - h \in \mathbb{Z}$.

We prove:
1. **Factorization (`evalSpin_eq_exp_mul_laplace`)**:
   $$\int_{\mathbb{R}} e^{h w_l + (h + J) w_r} \, d\mu_J(h) =
     e^{J w_r} \int_{\mathbb{R}} e^{h (w_l + w_r)} \, d\mu_J(h).$$
2. **Even-spin $\pi$-periodicity (`eval_shift_pi`)**:
   Because $\mu_J = 0$ for odd $J$, $\mathcal{G}_{\text{mon}}$ is invariant under opposite
   imaginary shifts by $\pi$:
   $$\mathcal{G}_{\text{mon}}(w_l - i\pi, w_r + i\pi) = \mathcal{G}_{\text{mon}}(w_l, w_r).$$
3. **The $s$-channel positivity bound (`norm_eval_le_evalReal`)**:
   Increasing $|\operatorname{Im}(w_l)|$ or $|\operatorname{Im}(w_r)|$ never increases the modulus
   of the correlator:
   $$\|\mathcal{G}_{\text{mon}}(w_l, w_r)\| \le
     \mathcal{G}_{\text{mon}}(\operatorname{Re}(w_l), \operatorname{Re}(w_r)).$$
4. **Canonical construction for `FourPointData` (`FourPointData.toMonomialFourPointData`,
   `FourPointData.toMonomialFourPointData_eval`)**:
   Every `FourPointData` with $\nu \ge 0$ maps canonically to a `MonomialFourPointData` whose
   evaluation on $\operatorname{UcPdisk}$ equals `correlator_pdisk`.
-/

open Real Complex Topology Set Metric MeasureTheory Filter
open scoped ComplexConjugate ENNReal

/-- A single complex monomial $e^{h w_l + (h + J) w_r}$ of left weight $h \in \mathbb{R}$ and spin
$J = \bar{h} - h \in \mathbb{Z}$. -/
noncomputable def monomialTerm (h : ℝ) (J : ℤ) (wl wr : ℂ) : ℂ :=
  Complex.exp ((h : ℂ) * wl + ((h + (J : ℝ) : ℝ) : ℂ) * wr)

/-- Real-valued monomial $e^{h \sigma_l + (h + J) \sigma_r}$ for real arguments
$\sigma_l, \sigma_r \in \mathbb{R}$. -/
noncomputable def monomialTermReal (h : ℝ) (J : ℤ) (σl σr : ℝ) : ℝ :=
  Real.exp (h * σl + (h + (J : ℝ)) * σr)

lemma monomialTermReal_pos (h : ℝ) (J : ℤ) (σl σr : ℝ) :
    0 < monomialTermReal h J σl σr :=
  Real.exp_pos _

lemma monomialTermReal_nonneg (h : ℝ) (J : ℤ) (σl σr : ℝ) :
    0 ≤ monomialTermReal h J σl σr :=
  (monomialTermReal_pos h J σl σr).le

lemma monomialTerm_ofReal (h : ℝ) (J : ℤ) (σl σr : ℝ) :
    monomialTerm h J (σl : ℂ) (σr : ℂ) = (monomialTermReal h J σl σr : ℂ) := by
  dsimp [monomialTerm, monomialTermReal]
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

lemma norm_monomialTerm (h : ℝ) (J : ℤ) (wl wr : ℂ) :
    ‖monomialTerm h J wl wr‖ = monomialTermReal h J wl.re wr.re := by
  dsimp [monomialTerm, monomialTermReal]
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.add_re, Complex.mul_re]

/-- Factorization of the monomial into the spin factor $e^{J w_r}$ and the twist factor
$e^{h (w_l + w_r)}$. -/
lemma monomialTerm_eq_exp_mul (h : ℝ) (J : ℤ) (wl wr : ℂ) :
    monomialTerm h J wl wr =
      Complex.exp ((J : ℂ) * wr) * Complex.exp ((h : ℂ) * (wl + wr)) := by
  dsimp [monomialTerm]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- For even spin $J$, `monomialTerm` is invariant under opposite imaginary shifts by $\pi$:
$(w_l, w_r) \mapsto (w_l - i\pi, w_r + i\pi)$. -/
lemma monomialTerm_shift_pi_of_even (h : ℝ) {J : ℤ} (hJ : Even J) (wl wr : ℂ) :
    monomialTerm h J (wl - π * I) (wr + π * I) = monomialTerm h J wl wr := by
  rcases hJ with ⟨k, rfl⟩
  dsimp [monomialTerm]
  have h_split :
      (h : ℂ) * (wl - π * I) + ((h + ((k + k : ℤ) : ℝ) : ℝ) : ℂ) * (wr + π * I) =
      ((h : ℂ) * wl + ((h + ((k + k : ℤ) : ℝ) : ℝ) : ℂ) * wr) +
        (k : ℂ) * (2 * π * I) := by
    push_cast
    ring
  rw [h_split, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Spectral data for the monomial decomposition of a four-point correlation function on
$\operatorname{UcPdisk}$, consisting of a family of non-negative measures $\mu_J$ on
$h \in \mathbb{R}$ indexed by spin $J = \bar{h} - h \in \mathbb{Z}$. -/
structure MonomialFourPointData where
  /-- Non-negative spectral measure $\mu_J$ over the left weight $h \in \mathbb{R}$ at spin
  $J \in \mathbb{Z}$. -/
  mu : ℤ → Measure ℝ

  /-- Unitarity support: both $h \ge 0$ and $\bar{h} = h + J \ge 0$ hold $\mu_J$-almost
  everywhere. -/
  support_unitary : ∀ J : ℤ, mu J { h : ℝ | h < 0 ∨ h + (J : ℝ) < 0 } = 0

  /-- Bose symmetry ($t \leftrightarrow u$ channel symmetry): odd spins $J$ have vanishing spectral
  measure. -/
  support_odd_spin : ∀ J : ℤ, Odd J → mu J = 0

  /-- Integrability of the real monomials on the negative real half-lines
  $\sigma_l < 0, \sigma_r < 0$. -/
  integrable_real : ∀ {σl σr : ℝ}, σl < 0 → σr < 0 → ∀ J : ℤ,
    Integrable (fun h : ℝ => monomialTermReal h J σl σr) (mu J)

  /-- Summability over spins $J \in \mathbb{Z}$ on the negative real half-lines
  $\sigma_l < 0, \sigma_r < 0$. -/
  summable_real : ∀ {σl σr : ℝ}, σl < 0 → σr < 0 →
    Summable (fun J : ℤ => ∫ h : ℝ, monomialTermReal h J σl σr ∂(mu J))

namespace MonomialFourPointData

variable (M : MonomialFourPointData)

/-- The Laplace transform of the spin-$J$ spectral measure $\mu_J$ at $w \in \operatorname{UcDisk}$:
$$L_J(w) = \int_{\mathbb{R}} e^{h w} \, d\mu_J(h).$$ -/
noncomputable def laplaceSpin (J : ℤ) (w : ℂ) : ℂ :=
  ∫ h : ℝ, Complex.exp ((h : ℂ) * w) ∂(M.mu J)

/-- The real-valued Laplace transform of the spin-$J$ spectral measure $\mu_J$ at
$\sigma \in \mathbb{R}$:
$$L_J(\sigma) = \int_{\mathbb{R}} e^{h \sigma} \, d\mu_J(h).$$ -/
noncomputable def laplaceSpinReal (J : ℤ) (σ : ℝ) : ℝ :=
  ∫ h : ℝ, Real.exp (h * σ) ∂(M.mu J)

/-- The spin-$J$ contribution to the monomial expansion at $(w_l, w_r)$:
$$\int_{\mathbb{R}} e^{h w_l + (h + J) w_r} \, d\mu_J(h).$$ -/
noncomputable def evalSpin (J : ℤ) (wl wr : ℂ) : ℂ :=
  ∫ h : ℝ, monomialTerm h J wl wr ∂(M.mu J)

/-- The real-valued spin-$J$ contribution at $(\sigma_l, \sigma_r) \in \mathbb{R}^2$. -/
noncomputable def evalSpinReal (J : ℤ) (σl σr : ℝ) : ℝ :=
  ∫ h : ℝ, monomialTermReal h J σl σr ∂(M.mu J)

/-- Full monomial evaluation on $(w_l, w_r) \in \operatorname{UcPdisk}$:
$$\mathcal{G}_{\text{mon}}(w_l, w_r) = \sum_{J \in \mathbb{Z}}
  \int_{\mathbb{R}} e^{h w_l + (h + J) w_r} \, d\mu_J(h).$$ -/
noncomputable def eval (wl wr : ℂ) : ℂ :=
  ∑' J : ℤ, M.evalSpin J wl wr

/-- Real-valued monomial evaluation at $(\sigma_l, \sigma_r) \in \mathbb{R}^2$. -/
noncomputable def evalReal (σl σr : ℝ) : ℝ :=
  ∑' J : ℤ, M.evalSpinReal J σl σr

/-- Factorization of the spin-$J$ contribution into $e^{J w_r}$ times `laplaceSpin`:
$$\int_{\mathbb{R}} e^{h w_l + (h + J) w_r} \, d\mu_J(h) =
  e^{J w_r} L_J(w_l + w_r).$$ -/
theorem evalSpin_eq_exp_mul_laplace (J : ℤ) (wl wr : ℂ) :
    M.evalSpin J wl wr = Complex.exp ((J : ℂ) * wr) * M.laplaceSpin J (wl + wr) := by
  dsimp [evalSpin, laplaceSpin]
  simp_rw [monomialTerm_eq_exp_mul]
  exact integral_const_mul _ _

/-- For odd spin $J$, `evalSpin` vanishes identically. -/
theorem evalSpin_of_odd {J : ℤ} (hJ : Odd J) (wl wr : ℂ) :
    M.evalSpin J wl wr = 0 := by
  dsimp [evalSpin]
  rw [M.support_odd_spin J hJ, integral_zero_measure]

/-- For odd spin $J$, `laplaceSpin` vanishes identically. -/
theorem laplaceSpin_of_odd {J : ℤ} (hJ : Odd J) (w : ℂ) :
    M.laplaceSpin J w = 0 := by
  dsimp [laplaceSpin]
  rw [M.support_odd_spin J hJ, integral_zero_measure]

/-- Each spin-$J$ contribution is invariant under $(w_l, w_r) \mapsto (w_l - i\pi, w_r + i\pi)$. -/
theorem evalSpin_shift_pi (J : ℤ) (wl wr : ℂ) :
    M.evalSpin J (wl - π * I) (wr + π * I) = M.evalSpin J wl wr := by
  rcases Int.even_or_odd J with hJ | hJ
  · dsimp [evalSpin]
    simp_rw [monomialTerm_shift_pi_of_even _ hJ]
  · rw [M.evalSpin_of_odd hJ, M.evalSpin_of_odd hJ]

/-- Even-spin $\pi$-periodicity of the monomial correlator under opposite imaginary shifts:
$$\mathcal{G}_{\text{mon}}(w_l - i\pi, w_r + i\pi) = \mathcal{G}_{\text{mon}}(w_l, w_r).$$ -/
theorem eval_shift_pi (wl wr : ℂ) :
    M.eval (wl - π * I) (wr + π * I) = M.eval wl wr := by
  dsimp [eval]
  simp_rw [M.evalSpin_shift_pi]

theorem laplaceSpinReal_nonneg (J : ℤ) (σ : ℝ) :
    0 ≤ M.laplaceSpinReal J σ :=
  integral_nonneg (fun h => (Real.exp_pos (h * σ)).le)

theorem evalSpinReal_nonneg (J : ℤ) (σl σr : ℝ) :
    0 ≤ M.evalSpinReal J σl σr :=
  integral_nonneg (fun h => monomialTermReal_nonneg h J σl σr)

theorem evalReal_nonneg (σl σr : ℝ) :
    0 ≤ M.evalReal σl σr :=
  tsum_nonneg (fun J => M.evalSpinReal_nonneg J σl σr)

theorem laplaceSpin_ofReal (J : ℤ) (σ : ℝ) :
    M.laplaceSpin J (σ : ℂ) = (M.laplaceSpinReal J σ : ℂ) := by
  dsimp [laplaceSpin, laplaceSpinReal]
  have h_eq : ∀ h : ℝ, Complex.exp ((h : ℂ) * (σ : ℂ)) = ((Real.exp (h * σ) : ℝ) : ℂ) := by
    intro h
    rw [Complex.ofReal_exp]
    push_cast
    rfl
  simp_rw [h_eq]
  exact integral_ofReal

theorem evalSpin_ofReal (J : ℤ) (σl σr : ℝ) :
    M.evalSpin J (σl : ℂ) (σr : ℂ) = (M.evalSpinReal J σl σr : ℂ) := by
  dsimp [evalSpin, evalSpinReal]
  simp_rw [monomialTerm_ofReal]
  exact integral_ofReal

theorem eval_ofReal (σl σr : ℝ) :
    M.eval (σl : ℂ) (σr : ℂ) = (M.evalReal σl σr : ℂ) := by
  dsimp [eval, evalReal]
  simp_rw [M.evalSpin_ofReal]
  exact (Complex.ofReal_tsum _).symm

/-- **1D Positivity Bound for `laplaceSpin`**: because $\mu_J$ is a non-negative measure,
increasing $|\operatorname{Im}(w)|$ never increases $\|L_J(w)\|$:
$$\|L_J(w)\| \le L_J(\operatorname{Re}(w)).$$ -/
theorem norm_laplaceSpin_le_laplaceSpinReal (J : ℤ) (w : ℂ) :
    ‖M.laplaceSpin J w‖ ≤ M.laplaceSpinReal J w.re := by
  dsimp [laplaceSpin, laplaceSpinReal]
  calc
    ‖∫ h : ℝ, Complex.exp ((h : ℂ) * w) ∂(M.mu J)‖
      ≤ ∫ h : ℝ, ‖Complex.exp ((h : ℂ) * w)‖ ∂(M.mu J) := norm_integral_le_integral_norm _
    _ = ∫ h : ℝ, Real.exp (h * w.re) ∂(M.mu J) := by
      congr 1
      ext h
      rw [Complex.norm_exp]
      simp [Complex.mul_re]

/-- Integrability of `monomialTerm` on $\operatorname{UcPdisk}$ for every spin
$J \in \mathbb{Z}$. -/
theorem integrable_monomialTerm {wl wr : ℂ} (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) (J : ℤ) :
    Integrable (fun h : ℝ => monomialTerm h J wl wr) (M.mu J) := by
  have h_real := M.integrable_real hwl hwr J
  have h_meas : AEStronglyMeasurable (fun h : ℝ => monomialTerm h J wl wr) (M.mu J) := by
    dsimp [monomialTerm]
    fun_prop
  refine h_real.mono h_meas ?_
  filter_upwards with h
  rw [norm_monomialTerm, Real.norm_of_nonneg (monomialTermReal_nonneg h J wl.re wr.re)]

/-- Triangle inequality bound for the spin-$J$ contribution on $\operatorname{UcPdisk}$. -/
theorem norm_evalSpin_le_evalSpinReal (J : ℤ) (wl wr : ℂ) :
    ‖M.evalSpin J wl wr‖ ≤ M.evalSpinReal J wl.re wr.re := by
  dsimp [evalSpin, evalSpinReal]
  calc
    ‖∫ h : ℝ, monomialTerm h J wl wr ∂(M.mu J)‖
      ≤ ∫ h : ℝ, ‖monomialTerm h J wl wr‖ ∂(M.mu J) := norm_integral_le_integral_norm _
    _ = ∫ h : ℝ, monomialTermReal h J wl.re wr.re ∂(M.mu J) := by
      simp_rw [norm_monomialTerm]

/-- Summability of `evalSpin` over $J \in \mathbb{Z}$ on $\operatorname{UcPdisk}$. -/
theorem summable_evalSpin {wl wr : ℂ} (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) :
    Summable (fun J : ℤ => M.evalSpin J wl wr) :=
  Summable.of_norm_bounded (M.summable_real hwl hwr)
    (fun J => M.norm_evalSpin_le_evalSpinReal J wl wr)

/-- **The $s$-channel positivity bound**: on $\operatorname{UcPdisk}$, increasing
$|\operatorname{Im}(w_l)|$ or $|\operatorname{Im}(w_r)|$ never increases the modulus of
$\mathcal{G}_{\text{mon}}$:
$$\|\mathcal{G}_{\text{mon}}(w_l, w_r)\| \le
  \mathcal{G}_{\text{mon}}(\operatorname{Re}(w_l), \operatorname{Re}(w_r)).$$ -/
theorem norm_eval_le_evalReal {wl wr : ℂ} (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) :
    ‖M.eval wl wr‖ ≤ M.evalReal wl.re wr.re := by
  dsimp [eval, evalReal]
  have h_sum_norm : Summable (fun J : ℤ => ‖M.evalSpin J wl wr‖) :=
    (M.summable_evalSpin hwl hwr).norm
  calc
    ‖∑' J : ℤ, M.evalSpin J wl wr‖
      ≤ ∑' J : ℤ, ‖M.evalSpin J wl wr‖ := norm_tsum_le_tsum_norm h_sum_norm
    _ ≤ ∑' J : ℤ, M.evalSpinReal J wl.re wr.re :=
      h_sum_norm.tsum_le_tsum (fun J => M.norm_evalSpin_le_evalSpinReal J wl wr)
        (M.summable_real hwl hwr)

/-- Continuity of the spin-$J$ contribution along opposite imaginary shifts
$\theta \mapsto (w_l - i\theta, w_r + i\theta)$ for $(w_l, w_r) \in \operatorname{UcPdisk}$. -/
theorem continuous_evalSpin_shift {wl wr : ℂ} (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) (J : ℤ) :
    Continuous (fun θ : ℝ => M.evalSpin J (wl - (θ : ℂ) * I) (wr + (θ : ℂ) * I)) := by
  dsimp [evalSpin]
  refine continuous_of_dominated
    (bound := fun h => monomialTermReal h J wl.re wr.re) ?_ ?_ (M.integrable_real hwl hwr J) ?_
  · intro θ
    dsimp [monomialTerm]
    fun_prop
  · intro θ
    filter_upwards with h
    rw [norm_monomialTerm]
    have h_wl_re : (wl - (θ : ℂ) * I).re = wl.re := by simp
    have h_wr_re : (wr + (θ : ℂ) * I).re = wr.re := by simp
    rw [h_wl_re, h_wr_re]
  · filter_upwards with h
    dsimp [monomialTerm]
    fun_prop

/-- Continuity of `M.eval` along opposite imaginary shifts
$\theta \mapsto (w_l - i\theta, w_r + i\theta)$ for $(w_l, w_r) \in \operatorname{UcPdisk}$. -/
theorem continuous_eval_shift {wl wr : ℂ} (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) :
    Continuous (fun θ : ℝ => M.eval (wl - (θ : ℂ) * I) (wr + (θ : ℂ) * I)) := by
  dsimp [eval]
  refine continuous_tsum (fun J => M.continuous_evalSpin_shift hwl hwr J)
    (M.summable_real hwl hwr) (fun J θ => ?_)
  have h_bound := M.norm_evalSpin_le_evalSpinReal J (wl - (θ : ℂ) * I) (wr + (θ : ℂ) * I)
  have h_wl_re : (wl - (θ : ℂ) * I).re = wl.re := by simp
  have h_wr_re : (wr + (θ : ℂ) * I).re = wr.re := by simp
  rwa [h_wl_re, h_wr_re] at h_bound

/-- Unitarity guarantees $h \ge 0$ almost everywhere with respect to $\mu_J$. -/
theorem ae_nonneg (J : ℤ) : ∀ᵐ h : ℝ ∂(M.mu J), 0 ≤ h := by
  have h_ae : ∀ᶠ h : ℝ in ae (M.mu J), h ∉ { h : ℝ | h < 0 ∨ h + (J : ℝ) < 0 } :=
    compl_mem_ae_iff.mpr (M.support_unitary J)
  filter_upwards [h_ae] with h hh
  exact not_lt.mp (fun hlt => hh (Or.inl hlt))

/-- Integrability of the real Laplace integrand $e^{h \sigma}$ with respect to $\mu_J$ for any
$\sigma < 0$. -/
theorem integrable_exp_real {σ : ℝ} (hσ : σ < 0) (J : ℤ) :
    Integrable (fun h : ℝ => Real.exp (h * σ)) (M.mu J) := by
  have hσ2 : σ / 2 < 0 := by linarith
  have h_int := (M.integrable_real hσ2 hσ2 J).const_mul (Real.exp (- (J : ℝ) * (σ / 2)))
  refine h_int.congr (Filter.Eventually.of_forall fun h => ?_)
  dsimp [monomialTermReal]
  rw [← Real.exp_add]
  congr 1
  ring

/-- Every spin-$J$ spectral measure $\mu_J$ is $\sigma$-finite, since $e^{-h}$ is $\mu_J$-integrable
and bounded below by $e^{-n} > 0$ on $(-\infty, n]$. -/
instance sigmaFinite_mu (J : ℤ) : SigmaFinite (M.mu J) := by
  refine ⟨⟨{
    set := fun n : ℕ => Iic (n : ℝ)
    set_mem := fun _ => trivial
    finite := fun n => ?_
    spanning := eq_univ_iff_forall.mpr fun x => mem_iUnion.mpr ⟨⌈x⌉₊, Nat.le_ceil x⟩
  }⟩⟩
  have h_int := M.integrable_exp_real (by norm_num : (-1 : ℝ) < 0) J
  refine lt_of_le_of_lt (measure_mono (fun h (hh : h ≤ (n : ℝ)) => ?_))
    (h_int.measure_ge_lt_top (Real.exp_pos (-(n : ℝ))))
  change Real.exp (-(n : ℝ)) ≤ Real.exp (h * (-1))
  exact Real.exp_le_exp.mpr (by linarith)

/-- Integrability of the complex Laplace integrand $e^{h w}$ with respect to $\mu_J$ for any
$w \in \operatorname{UcDisk}$. -/
theorem integrable_exp {w : ℂ} (hw : w ∈ UcDisk) (J : ℤ) :
    Integrable (fun h : ℝ => Complex.exp ((h : ℂ) * w)) (M.mu J) := by
  have h_real := M.integrable_exp_real hw J
  have h_meas : AEStronglyMeasurable (fun h : ℝ => Complex.exp ((h : ℂ) * w)) (M.mu J) := by
    fun_prop
  refine h_real.mono h_meas ?_
  filter_upwards with h
  rw [Complex.norm_exp, Real.norm_of_nonneg (Real.exp_pos _).le]
  simp [Complex.mul_re]

/-- Monotonicity of `laplaceSpinReal` on the negative real axis $\sigma_1 \le \sigma_2 < 0$. -/
theorem laplaceSpinReal_mono (J : ℤ) {σ₁ σ₂ : ℝ} (hσ₁ : σ₁ < 0) (hσ₂ : σ₂ < 0)
    (hle : σ₁ ≤ σ₂) :
    M.laplaceSpinReal J σ₁ ≤ M.laplaceSpinReal J σ₂ := by
  dsimp [laplaceSpinReal]
  refine integral_mono_ae (M.integrable_exp_real hσ₁ J) (M.integrable_exp_real hσ₂ J) ?_
  filter_upwards [M.ae_nonneg J] with h hh
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hle hh)

/-- Monotonicity of `evalSpinReal` in its first argument $\sigma_{l, 1} \le \sigma_{l, 2} < 0$. -/
theorem evalSpinReal_mono_left (J : ℤ) {σl₁ σl₂ σr : ℝ}
    (hσl₁ : σl₁ < 0) (hσl₂ : σl₂ < 0) (hσr : σr < 0) (hle : σl₁ ≤ σl₂) :
    M.evalSpinReal J σl₁ σr ≤ M.evalSpinReal J σl₂ σr := by
  dsimp [evalSpinReal, monomialTermReal]
  refine integral_mono_ae (M.integrable_real hσl₁ hσr J) (M.integrable_real hσl₂ hσr J) ?_
  filter_upwards [M.ae_nonneg J] with h hh
  exact Real.exp_le_exp.mpr (add_le_add_left (mul_le_mul_of_nonneg_left hle hh) _)

/-- Monotonicity of `evalReal` in its first argument $\sigma_{l, 1} \le \sigma_{l, 2} < 0$. -/
theorem evalReal_mono_left {σl₁ σl₂ σr : ℝ}
    (hσl₁ : σl₁ < 0) (hσl₂ : σl₂ < 0) (hσr : σr < 0) (hle : σl₁ ≤ σl₂) :
    M.evalReal σl₁ σr ≤ M.evalReal σl₂ σr :=
  (M.summable_real hσl₁ hσr).tsum_le_tsum
    (fun J => M.evalSpinReal_mono_left J hσl₁ hσl₂ hσr hle)
    (M.summable_real hσl₂ hσr)

/-- Holomorphy of `laplaceSpin` on $\operatorname{UcDisk} = \{\operatorname{Re}(w) < 0\}$. -/
theorem differentiableOn_laplaceSpin (J : ℤ) :
    DifferentiableOn ℂ (M.laplaceSpin J) UcDisk := by
  intro w₀ hw₀
  have hw₀_re : w₀.re < 0 := hw₀
  set σ : ℝ := w₀.re / 2
  have hσ_neg : σ < 0 := by dsimp [σ]; linarith
  set δ : ℝ := -σ / 2
  have hδ_pos : 0 < δ := by dsimp [δ]; linarith
  let s : Set ℂ := { w : ℂ | w.re < σ }
  have hs_open : IsOpen s := isOpen_lt Complex.continuous_re continuous_const
  have hw₀_s : w₀ ∈ s := by change w₀.re < w₀.re / 2; linarith
  have hs_nhds : s ∈ 𝓝 w₀ := hs_open.mem_nhds hw₀_s
  let F : ℂ → ℝ → ℂ := fun w h => Complex.exp ((h : ℂ) * w)
  let F' : ℂ → ℝ → ℂ := fun w h => (h : ℂ) * Complex.exp ((h : ℂ) * w)
  let bound : ℝ → ℝ := fun h => δ⁻¹ * Real.exp (h * (σ / 2))
  have h_deriv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := bound) hs_nhds
    (Filter.Eventually.of_forall fun w => by dsimp [F]; fun_prop)
    (M.integrable_exp hw₀ J)
    (by dsimp [F']; fun_prop)
    ?_ ?_ ?_
  · exact h_deriv.2.differentiableAt.differentiableWithinAt
  · filter_upwards [M.ae_nonneg J] with h hh w hw
    have hw_re : w.re < σ := hw
    dsimp [F', bound]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hh, Complex.norm_exp]
    have h_re : ((h : ℂ) * w).re = h * w.re := by simp [Complex.mul_re]
    rw [h_re]
    have h_h_le : h ≤ δ⁻¹ * Real.exp (h * δ) := by
      have h1 : h * δ ≤ Real.exp (h * δ) :=
        (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp (h * δ))
      calc
        h = δ⁻¹ * (h * δ) := by field_simp
        _ ≤ δ⁻¹ * Real.exp (h * δ) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hδ_pos.le)
    have h_exp_le : Real.exp (h * w.re) ≤ Real.exp (h * σ) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hw_re.le hh)
    calc
      h * Real.exp (h * w.re)
        ≤ (δ⁻¹ * Real.exp (h * δ)) * Real.exp (h * σ) :=
          mul_le_mul h_h_le h_exp_le (Real.exp_pos _).le (by positivity)
      _ = δ⁻¹ * Real.exp (h * (σ / 2)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        dsimp [δ]
        ring
  · exact (M.integrable_exp_real (by linarith : σ / 2 < 0) J).const_mul δ⁻¹
  · refine Filter.Eventually.of_forall fun h w _ => ?_
    dsimp [F, F']
    have h_id : HasDerivAt (fun z : ℂ => (h : ℂ) * z) (h : ℂ) w := by
      simpa using (hasDerivAt_id w).const_mul (h : ℂ)
    simpa [mul_comm] using h_id.cexp

end MonomialFourPointData

/-!
## Canonical Construction of `MonomialFourPointData` from `FourPointData`

Every `FourPointData` with $\nu = (d - 2)/2 \ge 0$ canonically induces a `MonomialFourPointData`
(`FourPointData.toMonomialFourPointData`) whose evaluation on $\operatorname{UcPdisk}$ equals
`corr.correlator_pdisk` (`FourPointData.toMonomialFourPointData_eval`).

### Mathematical Construction and Proof Strategy

1. **Expansion into Monomial Atoms (`MonomialIdx`)**:
   In `Blocks_pdisk.lean` and `Gegenbauers.lean`, each conformal block $G_{\Delta, l}^{\text{pdisk}}$
   is expanded over descendant level $n \in \mathbb{N}$, descendant spin $j \in S(l, n)$, and
   Gegenbauer binomial index $0 \le a \le j$:
   $$G_{\Delta, l}^{\text{pdisk}}(w_l, w_r) =
     \sum_{n=0}^{\infty} \sum_{j \in S(l, n)} \sum_{a=0}^{j}
       A_{n, j}(\Delta, l) \, c_{j, a}^{(\nu)} \,
       e^{h_{n, j, a}(\Delta) w_l + (h_{n, j, a}(\Delta) + J_{j, a}) w_r},$$
   where each triple $q = (n, j, a) \in \mathbb{N}^3$ (`MonomialIdx`) contributes a monomial of
   spin $J_{j, a} = j - 2a \in \mathbb{Z}$ (`monomialIdxSpin`) and left scaling weight
   $h_{n, j, a}(\Delta) = \frac{\Delta + n - j}{2} + a$ (`monomialIdxWeight`).

2. **Pushforward Measures (`monomialAtomMeasure` and `monomialMeasure`)**:
   For each triple $q = (n, j, a)$, weighting the primary OPE measure `corr.mu_measure` on
   $(\Delta, l) \in \mathbb{R} \times \mathbb{N}$ by the non-negative density
   $A_{n, j}(\Delta, l) \, c_{j, a}^{(\nu)}$ (`monomialIdxCoeff`) and pushing forward along the
   affine map $(\Delta, l) \mapsto h_{n, j, a}(\Delta)$ defines a Borel measure
   `corr.monomialAtomMeasure q` on $\mathbb{R}$. Summing over all $q \in \mathbb{N}^3$ in the fiber
   $j - 2a = J$ defines the spin-$J$ spectral measure `corr.monomialMeasure J`.

3. **Unitarity and Bose Symmetry (`monomialMeasure_support_unitary`,
   `monomialMeasure_support_odd_spin`)**:
   - Whenever $A_{n, j}(\Delta, l) \ne 0$ and $0 \le a \le j$, we have $j \in S(l, n)$ so
     $j \le l + n$. On the unitary support $\Delta \ge l$ of `corr.mu_measure`, this implies both
     $h = \frac{\Delta + n - j}{2} + a \ge a \ge 0$ and
     $h + J = \frac{\Delta + n - j}{2} + (j - a) \ge j - a \ge 0$.
   - By `corr.support_even_spin` ($l$ is even almost everywhere), `ConformalBlock.A_odd_level`
     ($A_{n, j} = 0$ for odd $n$), and the parity condition $j \equiv l + n \pmod{2}$ for
     $j \in S(l, n)$, every active descendant spin $j$ is even, and hence every active monomial spin
     $J = j - 2a$ is even. Thus `corr.monomialMeasure J = 0` for all odd $J$.

4. **Tonelli's Theorem and Fiberwise Summation (`summable_integral_monomialIdxRealTerm`,
   `toMonomialFourPointData_eval`)**:
   For any $\sigma_l < 0$ and $\sigma_r < 0$, all real monomial terms `monomialIdxRealTerm` are
   non-negative and sum over $q = (n, j, a) \in \mathbb{N}^3$ to
   $\operatorname{Re} G_{\Delta, l}^{\text{pdisk}}(\sigma_l, \sigma_r)$
   (`tsum_monomialIdxRealTerm_eq_re_evalPdisk`), which is `corr.mu_measure`-integrable by
   `corr.converges_correlator_pdisk`. Applying Tonelli's theorem (`lintegral_tsum`) shows that the
   integrated contributions $\int \operatorname{monomialIdxRealTerm}(q, \sigma_l, \sigma_r)\, d\mu$
   are summable over $q \in \mathbb{N}^3$. Partitioning $\mathbb{N}^3$ into fibers of
   $\operatorname{monomialIdxSpin}(q) = J$ (`hasSum_fiberwise_monomialIdxSpin`) and applying
   `integral_sum_measure` and `integral_tsum_of_summable_integral_norm` then yields both the
   finiteness axioms of `MonomialFourPointData` and the evaluation identity
   `(corr.toMonomialFourPointData hν).eval wl wr = corr.correlator_pdisk wl wr`.
-/

/-- Index triple $q = (n, j, a) \in \mathbb{N} \times \mathbb{N} \times \mathbb{N}$ for the
monomial expansion of a conformal block: descendant level $n$, descendant spin $j$, and
Gegenbauer binomial index $a \le j$. -/
abbrev MonomialIdx : Type := ℕ × ℕ × ℕ

/-- Monomial spin $J = j - 2a \in \mathbb{Z}$ associated to $q = (n, j, a)$. -/
def monomialIdxSpin (q : MonomialIdx) : ℤ :=
  (q.2.1 : ℤ) - 2 * (q.2.2 : ℤ)

/-- Left scaling weight $h(\Delta, l) = \frac{\Delta + n - j}{2} + a$ associated to
$q = (n, j, a)$. -/
noncomputable def monomialIdxWeight (q : MonomialIdx) (p : ℝ × ℕ) : ℝ :=
  (p.1 + (q.1 : ℝ) - (q.2.1 : ℝ)) / 2 + (q.2.2 : ℝ)

/-- Measurability of the affine weight map $p = (\Delta, l) \mapsto \frac{\Delta + n - j}{2} + a$. -/
lemma measurable_monomialIdxWeight (q : MonomialIdx) :
    Measurable (monomialIdxWeight q) := by
  unfold monomialIdxWeight
  fun_prop

/-- For $\nu \ge 0$, the Gegenbauer binomial coefficient `geg_two_var_coeff` is real, so casting its
real part back to $\mathbb{C}$ reproduces the coefficient. -/
lemma geg_two_var_coeff_ofReal_re {ν : ℝ} (hν : 0 ≤ ν) (j a : ℕ) :
    ((gegenbauer.geg_two_var_coeff (ν : ℂ) j a).re : ℂ) =
      gegenbauer.geg_two_var_coeff (ν : ℂ) j a := by
  apply Complex.ext
  · simp
  · simp [(gegenbauer.geg_two_var_coeff_nonneg ν hν j a).2]

namespace FourPointData

variable {ν Δ_phi : ℝ} (corr : FourPointData ν Δ_phi)

/-- Non-negative coefficient $A_{n, j}(\Delta, l) \, c_{j, a}^{(\nu)}$ of the monomial
$q = (n, j, a)$ at primary $(\Delta, l) = p$, set to $0$ when $a > j$. -/
noncomputable def monomialIdxCoeff (q : MonomialIdx) (p : ℝ × ℕ) : ℝ :=
  if q.2.2 ≤ q.2.1 then
    ((corr.blocks p.1 p.2).level q.1).A q.2.1 *
      (gegenbauer.geg_two_var_coeff (ν : ℂ) q.2.1 q.2.2).re
  else 0

/-- Measurability of `corr.monomialIdxCoeff q` across the primary spectrum. -/
lemma measurable_monomialIdxCoeff (q : MonomialIdx) :
    Measurable (corr.monomialIdxCoeff q) := by
  unfold monomialIdxCoeff
  by_cases h : q.2.2 ≤ q.2.1
  · simp only [h, ↓reduceIte]
    exact (corr.measurable_A q.1 q.2.1).mul measurable_const
  · simp only [h, ↓reduceIte]
    exact measurable_const

/-- Non-negativity of the conformal block expansion coefficients $A_{n, j}(\Delta, l) \ge 0$ for all
$n, j \in \mathbb{N}$ (vanishing outside `descendantSpins`). -/
lemma level_A_nonneg (p : ℝ × ℕ) (n j : ℕ) :
    0 ≤ ((corr.blocks p.1 p.2).level n).A j := by
  by_cases hj : j ∈ descendantSpins p.2 n
  · exact ((corr.blocks p.1 p.2).level n).A_nonneg j hj
  · rw [((corr.blocks p.1 p.2).level n).A_support j hj]

/-- Non-negativity of `corr.monomialIdxCoeff q p` when $\nu \ge 0$. -/
lemma monomialIdxCoeff_nonneg (hν : 0 ≤ ν) (q : MonomialIdx) (p : ℝ × ℕ) :
    0 ≤ corr.monomialIdxCoeff q p := by
  dsimp [monomialIdxCoeff]
  split_ifs with h
  · exact mul_nonneg (corr.level_A_nonneg p q.1 q.2.1)
      (gegenbauer.geg_two_var_coeff_nonneg ν hν q.2.1 q.2.2).1
  · exact le_rfl

/-- Pushforward measure on $h \in \mathbb{R}$ contributed by a single monomial index
$q = (n, j, a)$. -/
noncomputable def monomialAtomMeasure (q : MonomialIdx) : Measure ℝ :=
  (corr.mu_measure.withDensity (fun p => ENNReal.ofReal (corr.monomialIdxCoeff q p))).map
    (monomialIdxWeight q)

/-- Spin-$J$ monomial spectral measure $\mu_J$ obtained by summing `monomialAtomMeasure q` over all
triples $q = (n, j, a)$ with $j - 2a = J$. -/
noncomputable def monomialMeasure (J : ℤ) : Measure ℝ :=
  Measure.sum (fun q : MonomialIdx =>
    if monomialIdxSpin q = J then corr.monomialAtomMeasure q else 0)

/-- Characterization of Bochner integrability with respect to the pushforward measure
`corr.monomialAtomMeasure q` by pulling back to `corr.mu_measure`. -/
lemma integrable_monomialAtomMeasure_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hν : 0 ≤ ν) (q : MonomialIdx) {f : ℝ → E} (hf : Continuous f) :
    Integrable f (corr.monomialAtomMeasure q) ↔
      Integrable (fun p => corr.monomialIdxCoeff q p • f (monomialIdxWeight q p))
        corr.mu_measure := by
  dsimp [monomialAtomMeasure]
  rw [integrable_map_measure hf.aestronglyMeasurable (measurable_monomialIdxWeight q).aemeasurable]
  rw [integrable_withDensity_iff_integrable_smul'
    (corr.measurable_monomialIdxCoeff q).ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integrable_congr (Eventually.of_forall fun p => ?_)
  dsimp [Function.comp_def]
  rw [ENNReal.toReal_ofReal (corr.monomialIdxCoeff_nonneg hν q p)]

/-- Change-of-variables formula for the Bochner integral against the pushforward measure
`corr.monomialAtomMeasure q`. -/
lemma integral_monomialAtomMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hν : 0 ≤ ν) (q : MonomialIdx) {f : ℝ → E} (hf : Continuous f) :
    ∫ h, f h ∂(corr.monomialAtomMeasure q) =
      ∫ p, corr.monomialIdxCoeff q p • f (monomialIdxWeight q p) ∂corr.mu_measure := by
  dsimp [monomialAtomMeasure]
  rw [integral_map (measurable_monomialIdxWeight q).aemeasurable hf.aestronglyMeasurable]
  rw [integral_withDensity_eq_integral_toReal_smul
    (corr.measurable_monomialIdxCoeff q).ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  dsimp
  rw [ENNReal.toReal_ofReal (corr.monomialIdxCoeff_nonneg hν q p)]

/-- Almost everywhere primary spin $l$ is even with respect to `corr.mu_measure`. -/
lemma ae_even_spin : ∀ᵐ p : ℝ × ℕ ∂corr.mu_measure, Even p.2 := by
  rw [ae_iff]
  convert corr.support_even_spin using 2
  ext p
  exact Nat.not_even_iff_odd

/-- Unitarity support of `corr.monomialMeasure J`: both $h \ge 0$ and $\bar{h} = h + J \ge 0$ hold
almost everywhere because $\Delta \ge l$, $j \le l + n$, and $0 \le a \le j$. -/
lemma monomialMeasure_support_unitary (J : ℤ) :
    corr.monomialMeasure J { h : ℝ | h < 0 ∨ h + (J : ℝ) < 0 } = 0 := by
  let S : Set ℝ := { h : ℝ | h < 0 ∨ h + (J : ℝ) < 0 }
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_id measurable_const).union
      (measurableSet_lt (measurable_id.add measurable_const) measurable_const)
  change corr.monomialMeasure J S = 0
  dsimp [monomialMeasure]
  rw [Measure.sum_apply _ hS, ENNReal.tsum_eq_zero]
  intro q
  split_ifs with hJ
  · dsimp [monomialAtomMeasure]
    rw [Measure.map_apply (measurable_monomialIdxWeight q) hS,
      withDensity_apply _ ((measurable_monomialIdxWeight q) hS),
      setLIntegral_eq_zero_iff ((measurable_monomialIdxWeight q) hS)
        ((corr.measurable_monomialIdxCoeff q).ennreal_ofReal)]
    filter_upwards [corr.ae_unitary] with p hp h_mem
    rw [ENNReal.ofReal_eq_zero]
    refine le_of_eq ?_
    by_contra h_ne
    dsimp [monomialIdxCoeff] at h_ne
    split_ifs at h_ne with ha
    · have hj_mem : q.2.1 ∈ descendantSpins p.2 q.1 := by
        by_contra hj
        apply h_ne
        rw [((corr.blocks p.1 p.2).level q.1).A_support q.2.1 hj, zero_mul]
      have hj_le : (q.2.1 : ℝ) ≤ (p.2 : ℝ) + (q.1 : ℝ) := by
        exact_mod_cast (mem_descendantSpins.mp hj_mem).2.1
      have ha_le : (q.2.2 : ℝ) ≤ (q.2.1 : ℝ) := by exact_mod_cast ha
      have ha_nonneg : (0 : ℝ) ≤ (q.2.2 : ℝ) := Nat.cast_nonneg _
      have hJ_real : (J : ℝ) = (q.2.1 : ℝ) - 2 * (q.2.2 : ℝ) := by
        rw [← hJ]
        dsimp [monomialIdxSpin]
        push_cast
        ring
      rcases h_mem with h_lt | h_lt
      · dsimp [monomialIdxWeight] at h_lt
        linarith
      · dsimp [monomialIdxWeight] at h_lt
        linarith
    · exact h_ne rfl
  · simp

/-- Bose symmetry of `corr.monomialMeasure J`: for odd spin $J$, `monomialMeasure J = 0` because
primary spins $l$ are even (`support_even_spin`), odd descendant levels $n$ vanish (`A_odd_level`),
and $j \equiv l + n \pmod{2}$ on `descendantSpins l n`. -/
lemma monomialMeasure_support_odd_spin (J : ℤ) (hJ : Odd J) :
    corr.monomialMeasure J = 0 := by
  dsimp [monomialMeasure]
  have h_zero : (fun q : MonomialIdx =>
      if monomialIdxSpin q = J then corr.monomialAtomMeasure q else 0) =
      fun _ => (0 : Measure ℝ) := by
    ext q S hS
    simp only [Measure.coe_zero]
    split_ifs with hqJ
    · dsimp [monomialAtomMeasure]
      rw [Measure.map_apply (measurable_monomialIdxWeight q) hS,
        withDensity_apply _ ((measurable_monomialIdxWeight q) hS),
        setLIntegral_eq_zero_iff ((measurable_monomialIdxWeight q) hS)
          ((corr.measurable_monomialIdxCoeff q).ennreal_ofReal)]
      filter_upwards [corr.ae_even_spin] with p hp_even _
      rw [ENNReal.ofReal_eq_zero]
      refine le_of_eq ?_
      have hj_odd : Odd q.2.1 := by
        have h_odd_spin : Odd ((q.2.1 : ℤ) - 2 * (q.2.2 : ℤ)) := by
          rwa [← hqJ] at hJ
        rw [Int.odd_iff] at h_odd_spin
        rw [Nat.odd_iff]
        omega
      have hA_zero : ((corr.blocks p.1 p.2).level q.1).A q.2.1 = 0 := by
        rcases Nat.even_or_odd q.1 with hn_even | hn_odd
        · have hj_not_mem : q.2.1 ∉ descendantSpins p.2 q.1 := by
            intro hj_mem
            have h_mod := (mem_descendantSpins.mp hj_mem).2.2
            have h_sum_even : Even (p.2 + q.1) := hp_even.add hn_even
            have h1 : q.2.1 % 2 = 1 := Nat.odd_iff.mp hj_odd
            have h0 : (p.2 + q.1) % 2 = 0 := Nat.even_iff.mp h_sum_even
            omega
          exact ((corr.blocks p.1 p.2).level q.1).A_support q.2.1 hj_not_mem
        · exact (corr.blocks p.1 p.2).A_odd_level q.1 hn_odd q.2.1
      dsimp [monomialIdxCoeff]
      split_ifs
      · rw [hA_zero, zero_mul]
      · rfl
    · rfl
  rw [h_zero, Measure.sum_zero]

/-- Complex monomial contribution of index $q = (n, j, a)$ at primary $p = (\Delta, l)$. -/
noncomputable def monomialIdxComplexTerm (q : MonomialIdx) (wl wr : ℂ) (p : ℝ × ℕ) : ℂ :=
  (corr.monomialIdxCoeff q p : ℂ) *
    monomialTerm (monomialIdxWeight q p) (monomialIdxSpin q) wl wr

/-- Real monomial contribution of index $q = (n, j, a)$ at primary $p = (\Delta, l)$. -/
noncomputable def monomialIdxRealTerm (q : MonomialIdx) (σl σr : ℝ) (p : ℝ × ℕ) : ℝ :=
  corr.monomialIdxCoeff q p *
    monomialTermReal (monomialIdxWeight q p) (monomialIdxSpin q) σl σr

lemma monomialIdxRealTerm_nonneg (hν : 0 ≤ ν) (q : MonomialIdx) (σl σr : ℝ) (p : ℝ × ℕ) :
    0 ≤ corr.monomialIdxRealTerm q σl σr p :=
  mul_nonneg (corr.monomialIdxCoeff_nonneg hν q p)
    (monomialTermReal_nonneg (monomialIdxWeight q p) (monomialIdxSpin q) σl σr)

lemma norm_monomialIdxComplexTerm (hν : 0 ≤ ν) (q : MonomialIdx) (wl wr : ℂ) (p : ℝ × ℕ) :
    ‖corr.monomialIdxComplexTerm q wl wr p‖ = corr.monomialIdxRealTerm q wl.re wr.re p := by
  dsimp [monomialIdxComplexTerm, monomialIdxRealTerm]
  rw [norm_mul, Complex.norm_of_nonneg (corr.monomialIdxCoeff_nonneg hν q p), norm_monomialTerm]

lemma monomialIdxComplexTerm_ofReal (q : MonomialIdx) (σl σr : ℝ) (p : ℝ × ℕ) :
    corr.monomialIdxComplexTerm q (σl : ℂ) (σr : ℂ) p =
      (corr.monomialIdxRealTerm q σl σr p : ℂ) := by
  dsimp [monomialIdxComplexTerm, monomialIdxRealTerm]
  rw [monomialTerm_ofReal, Complex.ofReal_mul]

/-- At fixed primary $p = (\Delta, l)$ and descendant level $n$, `monomialIdxCoeff` vanishes
outside the finite set $\operatorname{descendantSpins}(l, n) \times \{0, \dots, l + n\}$. -/
lemma monomialIdxCoeff_eq_zero_of_not_mem (n : ℕ) (ja : ℕ × ℕ) (p : ℝ × ℕ)
    (h : ja ∉ descendantSpins p.2 n ×ˢ Finset.range (p.2 + n + 1)) :
    corr.monomialIdxCoeff (n, ja.1, ja.2) p = 0 := by
  dsimp [monomialIdxCoeff]
  split_ifs with ha
  · have hj_not : ja.1 ∉ descendantSpins p.2 n := by
      intro hj_mem
      apply h
      rw [Finset.mem_product, Finset.mem_range]
      refine ⟨hj_mem, ?_⟩
      have hj_le := (mem_descendantSpins.mp hj_mem).2.1
      omega
    rw [((corr.blocks p.1 p.2).level n).A_support ja.1 hj_not, zero_mul]
  · rfl

lemma summable_monomialIdxComplexTerm_level (n : ℕ) (wl wr : ℂ) (p : ℝ × ℕ) :
    Summable (fun ja : ℕ × ℕ => corr.monomialIdxComplexTerm (n, ja.1, ja.2) wl wr p) := by
  refine summable_of_ne_finset_zero
    (s := descendantSpins p.2 n ×ˢ Finset.range (p.2 + n + 1)) (fun ja hja => ?_)
  dsimp [monomialIdxComplexTerm]
  rw [corr.monomialIdxCoeff_eq_zero_of_not_mem n ja p hja, Complex.ofReal_zero, zero_mul]

lemma summable_monomialIdxRealTerm_level (n : ℕ) (σl σr : ℝ) (p : ℝ × ℕ) :
    Summable (fun ja : ℕ × ℕ => corr.monomialIdxRealTerm (n, ja.1, ja.2) σl σr p) := by
  refine summable_of_ne_finset_zero
    (s := descendantSpins p.2 n ×ˢ Finset.range (p.2 + n + 1)) (fun ja hja => ?_)
  dsimp [monomialIdxRealTerm]
  rw [corr.monomialIdxCoeff_eq_zero_of_not_mem n ja p hja, zero_mul]

/-- Summing `monomialIdxComplexTerm` over $(j, a) \in \mathbb{N} \times \mathbb{N}$ at fixed
descendant level $n$ reproduces the polydisk level contribution `evalTermPdisk`. -/
lemma tsum_monomialIdxComplexTerm_level_eq_evalTermPdisk
    (hν : 0 ≤ ν) (p : ℝ × ℕ) (n : ℕ) (wl wr : ℂ) :
    (∑' ja : ℕ × ℕ, corr.monomialIdxComplexTerm (n, ja.1, ja.2) wl wr p) =
      ((corr.blocks p.1 p.2).level n).evalTermPdisk ν p.1 wl wr := by
  rw [tsum_eq_sum (s := descendantSpins p.2 n ×ˢ Finset.range (p.2 + n + 1)) (fun ja hja => by
    dsimp [monomialIdxComplexTerm]
    rw [corr.monomialIdxCoeff_eq_zero_of_not_mem n ja p hja, Complex.ofReal_zero, zero_mul])]
  rw [Finset.sum_product]
  dsimp [ConformalBlockLevel.evalTermPdisk, gegenbauer.geg_two_var_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj_le : j ≤ p.2 + n := (mem_descendantSpins.mp hj).2.1
  rw [Finset.mul_sum]
  have h_sub : Finset.range (j + 1) ⊆ Finset.range (p.2 + n + 1) :=
    Finset.range_mono (by omega)
  rw [← Finset.sum_subset h_sub (fun a _ ha_not => by
    have ha_gt : ¬ a ≤ j := by
      rw [Finset.mem_range] at ha_not
      omega
    dsimp [monomialIdxComplexTerm, monomialIdxCoeff]
    simp [ha_gt])]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha_le : a ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  dsimp [monomialIdxComplexTerm, monomialIdxCoeff, monomialTerm, monomialIdxWeight, monomialIdxSpin]
  simp only [ha_le, ↓reduceIte, Complex.ofReal_mul, geg_two_var_coeff_ofReal_re hν]
  rw [← Complex.exp_nat_mul wl a, ← Complex.exp_nat_mul wr (j - a)]
  have h_exp :
      Complex.exp ((((p.1 + (n : ℝ) - (j : ℝ)) / 2 + (a : ℝ) : ℝ) : ℂ) * wl +
          ((((p.1 + (n : ℝ) - (j : ℝ)) / 2 + (a : ℝ) + ((j : ℤ) - 2 * (a : ℤ) : ℤ) : ℝ) : ℂ) *
            wr)) =
        Complex.exp ((((p.1 + (n : ℝ) - (j : ℝ)) / 2 : ℝ) : ℂ) * wl) *
          Complex.exp ((((p.1 + (n : ℝ) - (j : ℝ)) / 2 : ℝ) : ℂ) * wr) *
          Complex.exp ((a : ℂ) * wl) *
          Complex.exp (((j - a : ℕ) : ℂ) * wr) := by
    repeat rw [← Complex.exp_add]
    congr 1
    rw [Nat.cast_sub ha_le]
    push_cast
    ring
  rw [h_exp]
  ring

/-- Real-axis specialization of `tsum_monomialIdxComplexTerm_level_eq_evalTermPdisk`. -/
lemma tsum_monomialIdxRealTerm_level_eq_re_evalTermPdisk
    (hν : 0 ≤ ν) (p : ℝ × ℕ) (n : ℕ) (σl σr : ℝ) :
    (∑' ja : ℕ × ℕ, corr.monomialIdxRealTerm (n, ja.1, ja.2) σl σr p) =
      (((corr.blocks p.1 p.2).level n).evalTermPdisk ν p.1 (σl : ℂ) (σr : ℂ)).re := by
  have h_eq := corr.tsum_monomialIdxComplexTerm_level_eq_evalTermPdisk hν p n (σl : ℂ) (σr : ℂ)
  simp_rw [corr.monomialIdxComplexTerm_ofReal] at h_eq
  rw [← Complex.ofReal_tsum] at h_eq
  exact congrArg Complex.re h_eq

/-- Summability of `monomialIdxRealTerm` over all $q = (n, j, a) \in \mathbb{N}^3$ at fixed primary
$p = (\Delta, l)$ satisfying $(l : \mathbb{R}) \le \Delta$ and negative real arguments
$\sigma_l < 0, \sigma_r < 0$. -/
lemma summable_monomialIdxRealTerm (hν : 0 ≤ ν) {σl σr : ℝ} (hσl : σl < 0) (hσr : σr < 0)
    (p : ℝ × ℕ) (hp : (p.2 : ℝ) ≤ p.1) :
    Summable (fun q : MonomialIdx => corr.monomialIdxRealTerm q σl σr p) := by
  have hwl : (σl : ℂ) ∈ UcDisk := by simpa [UcDisk] using hσl
  have hwr : (σr : ℂ) ∈ UcDisk := by simpa [UcDisk] using hσr
  have h_sum_level : Summable (fun n : ℕ =>
      ∑' ja : ℕ × ℕ, corr.monomialIdxRealTerm (n, ja.1, ja.2) σl σr p) := by
    simp_rw [corr.tsum_monomialIdxRealTerm_level_eq_re_evalTermPdisk hν p _ σl σr]
    exact Complex.reCLM.summable ((corr.blocks p.1 p.2).summable_evalTermPdisk hν hp hwl hwr)
  exact (summable_prod_of_nonneg
    (fun q => corr.monomialIdxRealTerm_nonneg hν q σl σr p)).mpr
    ⟨fun n => corr.summable_monomialIdxRealTerm_level n σl σr p, h_sum_level⟩

/-- Summing `monomialIdxRealTerm` over all $q = (n, j, a) \in \mathbb{N}^3$ reproduces the real part
of `evalPdisk` at $(\sigma_l, \sigma_r)$. -/
lemma tsum_monomialIdxRealTerm_eq_re_evalPdisk (hν : 0 ≤ ν) {σl σr : ℝ}
    (hσl : σl < 0) (hσr : σr < 0) (p : ℝ × ℕ) (hp : (p.2 : ℝ) ≤ p.1) :
    (∑' q : MonomialIdx, corr.monomialIdxRealTerm q σl σr p) =
      ((corr.blocks p.1 p.2).evalPdisk (σl : ℂ) (σr : ℂ)).re := by
  have hwl : (σl : ℂ) ∈ UcDisk := by simpa [UcDisk] using hσl
  have hwr : (σr : ℂ) ∈ UcDisk := by simpa [UcDisk] using hσr
  rw [(corr.summable_monomialIdxRealTerm hν hσl hσr p hp).tsum_prod'
    (fun n => corr.summable_monomialIdxRealTerm_level n σl σr p)]
  simp_rw [corr.tsum_monomialIdxRealTerm_level_eq_re_evalTermPdisk hν p _ σl σr]
  dsimp [ConformalBlock.evalPdisk]
  exact (Complex.reCLM.map_tsum
    ((corr.blocks p.1 p.2).summable_evalTermPdisk hν hp hwl hwr)).symm

/-- Summability of `monomialIdxComplexTerm` over all $q = (n, j, a) \in \mathbb{N}^3$ on
$\operatorname{UcPdisk}$. -/
lemma summable_monomialIdxComplexTerm (hν : 0 ≤ ν) {wl wr : ℂ}
    (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) (p : ℝ × ℕ) (hp : (p.2 : ℝ) ≤ p.1) :
    Summable (fun q : MonomialIdx => corr.monomialIdxComplexTerm q wl wr p) := by
  refine Summable.of_norm_bounded (corr.summable_monomialIdxRealTerm hν hwl hwr p hp) (fun q => ?_)
  exact (corr.norm_monomialIdxComplexTerm hν q wl wr p).le

/-- Summing `monomialIdxComplexTerm` over all $q = (n, j, a) \in \mathbb{N}^3$ at fixed primary
$p = (\Delta, l)$ reproduces `evalPdisk wl wr`. -/
lemma tsum_monomialIdxComplexTerm_eq_evalPdisk (hν : 0 ≤ ν) {wl wr : ℂ}
    (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) (p : ℝ × ℕ) (hp : (p.2 : ℝ) ≤ p.1) :
    (∑' q : MonomialIdx, corr.monomialIdxComplexTerm q wl wr p) =
      (corr.blocks p.1 p.2).evalPdisk wl wr := by
  rw [(corr.summable_monomialIdxComplexTerm hν hwl hwr p hp).tsum_prod'
    (fun n => corr.summable_monomialIdxComplexTerm_level n wl wr p)]
  simp_rw [corr.tsum_monomialIdxComplexTerm_level_eq_evalTermPdisk hν p _ wl wr]
  rfl

lemma measurable_monomialIdxRealTerm (q : MonomialIdx) (σl σr : ℝ) :
    Measurable (corr.monomialIdxRealTerm q σl σr) := by
  unfold monomialIdxRealTerm monomialTermReal
  refine (corr.measurable_monomialIdxCoeff q).mul ?_
  have h_w := measurable_monomialIdxWeight q
  fun_prop

lemma measurable_monomialIdxComplexTerm (q : MonomialIdx) (wl wr : ℂ) :
    Measurable (corr.monomialIdxComplexTerm q wl wr) := by
  unfold monomialIdxComplexTerm monomialTerm
  refine (Complex.measurable_ofReal.comp (corr.measurable_monomialIdxCoeff q)).mul ?_
  have h_w := measurable_monomialIdxWeight q
  fun_prop

/-- Integrability of `monomialIdxRealTerm q σl σr` with respect to `corr.mu_measure`, obtained by
bounding the single non-negative term $q$ by the full sum `evalPdisk (σl : ℂ) (σr : ℂ)`. -/
lemma integrable_monomialIdxRealTerm (hν : 0 ≤ ν) {σl σr : ℝ}
    (hσl : σl < 0) (hσr : σr < 0) (q : MonomialIdx) :
    Integrable (corr.monomialIdxRealTerm q σl σr) corr.mu_measure := by
  have hwl : (σl : ℂ) ∈ UcDisk := by simpa [UcDisk] using hσl
  have hwr : (σr : ℂ) ∈ UcDisk := by simpa [UcDisk] using hσr
  refine (corr.converges_correlator_pdisk hν hwl hwr).norm.mono'
    (corr.measurable_monomialIdxRealTerm q σl σr).aestronglyMeasurable ?_
  filter_upwards [corr.ae_unitary] with p hp
  rw [Real.norm_of_nonneg (corr.monomialIdxRealTerm_nonneg hν q σl σr p)]
  calc
    corr.monomialIdxRealTerm q σl σr p
      ≤ ∑' q' : MonomialIdx, corr.monomialIdxRealTerm q' σl σr p :=
        (corr.summable_monomialIdxRealTerm hν hσl hσr p hp).le_tsum q
          (fun q' _ => corr.monomialIdxRealTerm_nonneg hν q' σl σr p)
    _ = ((corr.blocks p.1 p.2).evalPdisk (σl : ℂ) (σr : ℂ)).re :=
        corr.tsum_monomialIdxRealTerm_eq_re_evalPdisk hν hσl hσr p hp
    _ ≤ ‖(corr.blocks p.1 p.2).evalPdisk (σl : ℂ) (σr : ℂ)‖ :=
        Complex.re_le_norm _

/-- Integrability of `monomialIdxComplexTerm q wl wr` with respect to `corr.mu_measure`. -/
lemma integrable_monomialIdxComplexTerm (hν : 0 ≤ ν) {wl wr : ℂ}
    (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) (q : MonomialIdx) :
    Integrable (corr.monomialIdxComplexTerm q wl wr) corr.mu_measure := by
  refine (corr.integrable_monomialIdxRealTerm hν hwl hwr q).mono'
    (corr.measurable_monomialIdxComplexTerm q wl wr).aestronglyMeasurable
    (Eventually.of_forall fun p => ?_)
  exact (corr.norm_monomialIdxComplexTerm hν q wl wr p).le

/-- Master Tonelli summability lemma: for $\sigma_l < 0, \sigma_r < 0$, the integrated real monomial
contributions $\int \operatorname{monomialIdxRealTerm}(q, \sigma_l, \sigma_r)\, d\mu$ are summable
over all triples $q = (n, j, a) \in \mathbb{N}^3$. -/
lemma summable_integral_monomialIdxRealTerm (hν : 0 ≤ ν) {σl σr : ℝ}
    (hσl : σl < 0) (hσr : σr < 0) :
    Summable (fun q : MonomialIdx => ∫ p, corr.monomialIdxRealTerm q σl σr p ∂corr.mu_measure) := by
  have hwl : (σl : ℂ) ∈ UcDisk := by simpa [UcDisk] using hσl
  have hwr : (σr : ℂ) ∈ UcDisk := by simpa [UcDisk] using hσr
  have h_nonneg (q : MonomialIdx) :
      0 ≤ ∫ p, corr.monomialIdxRealTerm q σl σr p ∂corr.mu_measure :=
    integral_nonneg (corr.monomialIdxRealTerm_nonneg hν q σl σr)
  have h_eq : (fun q : MonomialIdx => ∫ p, corr.monomialIdxRealTerm q σl σr p ∂corr.mu_measure) =
      fun q : MonomialIdx =>
        (ENNReal.ofReal (∫ p, corr.monomialIdxRealTerm q σl σr p ∂corr.mu_measure)).toReal := by
    ext q
    exact (ENNReal.toReal_ofReal (h_nonneg q)).symm
  rw [h_eq]
  refine ENNReal.summable_toReal ?_
  have h_lint (q : MonomialIdx) :
      ENNReal.ofReal (∫ p, corr.monomialIdxRealTerm q σl σr p ∂corr.mu_measure) =
        ∫⁻ p, ENNReal.ofReal (corr.monomialIdxRealTerm q σl σr p) ∂corr.mu_measure :=
    ofReal_integral_eq_lintegral_ofReal (corr.integrable_monomialIdxRealTerm hν hσl hσr q)
      (Eventually.of_forall (corr.monomialIdxRealTerm_nonneg hν q σl σr))
  simp_rw [h_lint]
  rw [← lintegral_tsum
    (fun q => (corr.measurable_monomialIdxRealTerm q σl σr).ennreal_ofReal.aemeasurable)]
  refine ne_of_lt (lt_of_le_of_lt (lintegral_mono_ae ?_)
    (corr.converges_correlator_pdisk hν hwl hwr).norm.hasFiniteIntegral)
  filter_upwards [corr.ae_unitary] with p hp
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun q => corr.monomialIdxRealTerm_nonneg hν q σl σr p)
    (corr.summable_monomialIdxRealTerm hν hσl hσr p hp),
    corr.tsum_monomialIdxRealTerm_eq_re_evalPdisk hν hσl hσr p hp,
    ← ofReal_norm, Real.norm_of_nonneg (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (Complex.re_le_norm _)

/-- Partitioning a summable series over $q \in \operatorname{MonomialIdx}$ into fibers of
$\operatorname{monomialIdxSpin}(q) = J \in \mathbb{Z}$. -/
lemma hasSum_fiberwise_monomialIdxSpin {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : MonomialIdx → E} {a : E} (hf : HasSum f a) :
    HasSum (fun J : ℤ => ∑' q : MonomialIdx, if monomialIdxSpin q = J then f q else 0) a := by
  convert hf.tsum_fiberwise monomialIdxSpin with J
  rw [tsum_subtype (monomialIdxSpin ⁻¹' {J}) f]
  congr 1
  ext q
  simp [Set.indicator]

/-- Integrability of `monomialTermReal` with respect to `corr.monomialMeasure J` for
$\sigma_l < 0, \sigma_r < 0$. -/
lemma monomialMeasure_integrable_real (hν : 0 ≤ ν) {σl σr : ℝ}
    (hσl : σl < 0) (hσr : σr < 0) (J : ℤ) :
    Integrable (fun h : ℝ => monomialTermReal h J σl σr) (corr.monomialMeasure J) := by
  dsimp [monomialMeasure]
  have hf_cont : Continuous (fun h : ℝ => monomialTermReal h J σl σr) := by
    unfold monomialTermReal
    fun_prop
  refine integrable_sum_measure (fun q => ?_) ?_
  · split_ifs with hq
    · rw [corr.integrable_monomialAtomMeasure_iff hν q hf_cont]
      subst hq
      exact corr.integrable_monomialIdxRealTerm hν hσl hσr q
    · exact integrable_zero_measure
  · refine (corr.summable_integral_monomialIdxRealTerm hν hσl hσr).of_nonneg_of_le
      (fun q => integral_nonneg fun _ => norm_nonneg _) (fun q => ?_)
    split_ifs with hq
    · have h_norm : (fun x : ℝ => ‖monomialTermReal x J σl σr‖) =
          fun x : ℝ => monomialTermReal x J σl σr := by
        ext x
        exact Real.norm_of_nonneg (monomialTermReal_nonneg x J σl σr)
      rw [h_norm, corr.integral_monomialAtomMeasure hν q hf_cont]
      simp [monomialIdxRealTerm, hq]
    · rw [integral_zero_measure]
      exact integral_nonneg (corr.monomialIdxRealTerm_nonneg hν q σl σr)

/-- Expansion of the spin-$J$ real monomial integral as a sum over the fiber
$\operatorname{monomialIdxSpin}(q) = J$. -/
lemma monomialMeasure_integral_real (hν : 0 ≤ ν) {σl σr : ℝ}
    (hσl : σl < 0) (hσr : σr < 0) (J : ℤ) :
    (∫ h : ℝ, monomialTermReal h J σl σr ∂(corr.monomialMeasure J)) =
      ∑' q : MonomialIdx,
        if monomialIdxSpin q = J then
          ∫ p, corr.monomialIdxRealTerm q σl σr p ∂corr.mu_measure
        else 0 := by
  have h_int := corr.monomialMeasure_integrable_real hν hσl hσr J
  dsimp [monomialMeasure] at h_int ⊢
  rw [integral_sum_measure h_int]
  have hf_cont : Continuous (fun h : ℝ => monomialTermReal h J σl σr) := by
    unfold monomialTermReal
    fun_prop
  congr 1 with q
  split_ifs with hq
  · rw [corr.integral_monomialAtomMeasure hν q hf_cont]
    simp [monomialIdxRealTerm, hq]
  · exact integral_zero_measure _

/-- Summability over spins $J \in \mathbb{Z}$ of the real monomial integrals for
$\sigma_l < 0, \sigma_r < 0$. -/
lemma monomialMeasure_summable_real (hν : 0 ≤ ν) {σl σr : ℝ}
    (hσl : σl < 0) (hσr : σr < 0) :
    Summable (fun J : ℤ => ∫ h : ℝ, monomialTermReal h J σl σr ∂(corr.monomialMeasure J)) := by
  simp_rw [corr.monomialMeasure_integral_real hν hσl hσr]
  exact (hasSum_fiberwise_monomialIdxSpin
    (corr.summable_integral_monomialIdxRealTerm hν hσl hσr).hasSum).summable

/-- Canonical `MonomialFourPointData` associated to a `FourPointData` with $\nu \ge 0$,
obtained by pushing forward `corr.mu_measure` along the descendant-level and Gegenbauer-monomial
weights and summing over all indices $q = (n, j, a)$ with $j - 2a = J$. -/
noncomputable def toMonomialFourPointData (hν : 0 ≤ ν) : MonomialFourPointData where
  mu := corr.monomialMeasure
  support_unitary := corr.monomialMeasure_support_unitary
  support_odd_spin := corr.monomialMeasure_support_odd_spin
  integrable_real := fun hσl hσr J => corr.monomialMeasure_integrable_real hν hσl hσr J
  summable_real := fun hσl hσr => corr.monomialMeasure_summable_real hν hσl hσr

/-- Expansion of the spin-$J$ complex monomial integral `evalSpin J wl wr` as a sum over the fiber
$\operatorname{monomialIdxSpin}(q) = J$. -/
lemma toMonomialFourPointData_evalSpin (hν : 0 ≤ ν) {wl wr : ℂ}
    (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) (J : ℤ) :
    (corr.toMonomialFourPointData hν).evalSpin J wl wr =
      ∑' q : MonomialIdx,
        if monomialIdxSpin q = J then
          ∫ p, corr.monomialIdxComplexTerm q wl wr p ∂corr.mu_measure
        else 0 := by
  have h_int := (corr.toMonomialFourPointData hν).integrable_monomialTerm hwl hwr J
  dsimp [MonomialFourPointData.evalSpin, toMonomialFourPointData, monomialMeasure] at h_int ⊢
  rw [integral_sum_measure h_int]
  have hf_cont : Continuous (fun h : ℝ => monomialTerm h J wl wr) := by
    unfold monomialTerm
    fun_prop
  congr 1 with q
  split_ifs with hq
  · rw [corr.integral_monomialAtomMeasure hν q hf_cont]
    simp [monomialIdxComplexTerm, Complex.real_smul, hq]
  · exact integral_zero_measure _

/-- Evaluating `corr.toMonomialFourPointData hν` on $\operatorname{UcPdisk}$ reproduces
`corr.correlator_pdisk`. -/
theorem toMonomialFourPointData_eval (hν : 0 ≤ ν) {wl wr : ℂ}
    (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) :
    (corr.toMonomialFourPointData hν).eval wl wr = corr.correlator_pdisk wl wr := by
  dsimp [MonomialFourPointData.eval, correlator_pdisk, eval_correlator_pdisk]
  simp_rw [corr.toMonomialFourPointData_evalSpin hν hwl hwr]
  have h_sum_norm : Summable (fun q : MonomialIdx =>
      ∫ p, ‖corr.monomialIdxComplexTerm q wl wr p‖ ∂corr.mu_measure) := by
    simp_rw [corr.norm_monomialIdxComplexTerm hν _ wl wr]
    exact corr.summable_integral_monomialIdxRealTerm hν hwl hwr
  have h_sum_complex : Summable (fun q : MonomialIdx =>
      ∫ p, corr.monomialIdxComplexTerm q wl wr p ∂corr.mu_measure) :=
    Summable.of_norm_bounded h_sum_norm (fun q => norm_integral_le_integral_norm _)
  rw [(hasSum_fiberwise_monomialIdxSpin h_sum_complex.hasSum).tsum_eq]
  refine (integral_tsum_of_summable_integral_norm
    (fun q => corr.integrable_monomialIdxComplexTerm hν hwl hwr q) h_sum_norm).trans ?_
  refine integral_congr_ae (corr.ae_unitary.mono fun p hp => ?_)
  exact corr.tsum_monomialIdxComplexTerm_eq_evalPdisk hν hwl hwr p hp

/-- Every `FourPointData` with $\nu \ge 0$ admits a monomial decomposition
`M : MonomialFourPointData` whose evaluation on $\operatorname{UcPdisk}$ agrees with
`corr.correlator_pdisk`. -/
theorem exists_monomialDecomp (hν : 0 ≤ ν) :
    ∃ M : MonomialFourPointData,
      ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
        M.eval wl wr = corr.correlator_pdisk wl wr :=
  ⟨corr.toMonomialFourPointData hν, fun hwl hwr => corr.toMonomialFourPointData_eval hν hwl hwr⟩

end FourPointData
