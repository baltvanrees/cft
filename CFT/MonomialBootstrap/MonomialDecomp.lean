/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Balt van Rees
-/
import Mathlib.Analysis.Calculus.ParametricIntegral
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
4. **Existence for `FourPointData` (`FourPointData.exists_monomialDecomp`)**:
   Every `FourPointData` admits a `MonomialFourPointData` agreeing with `correlator_pdisk` on
   $\operatorname{UcPdisk}$.
-/

open Real Complex Topology Set Metric MeasureTheory
open scoped ComplexConjugate

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

namespace FourPointData

variable {ν Δ_phi : ℝ} (corr : FourPointData ν Δ_phi)

/-- Every `FourPointData` with $\nu \ge 0$ admits a monomial decomposition
`M : MonomialFourPointData` whose evaluation on $\operatorname{UcPdisk}$ agrees with
`corr.correlator_pdisk`. -/
theorem exists_monomialDecomp (hν : 0 ≤ ν) :
    ∃ M : MonomialFourPointData,
      ∀ {wl wr : ℂ}, wl ∈ UcDisk → wr ∈ UcDisk →
        M.eval wl wr = corr.correlator_pdisk wl wr := by
  sorry

end FourPointData

