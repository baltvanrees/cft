/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Balt van Rees
-/
import CFT.LightconeBootstrap.LightconeBlock.Decomp
import CFT.LightconeBootstrap.Monomial.LaplaceBound

/-!
# Convergent Inner-Derivative Transmutation Operator and Endpoint Bounds

This file develops the inner-derivative representation of the 1D fractional transmutation operator
and establishes its low-$x$ and high-$x$ endpoint bounds:

1. **Inner-Derivative Transmutation Operator (`eulerD`, `transmuteInnerKernel`,
   `transmuteInnerDiff`, `transmuteOpInner`)**:
   At $\delta = 0$ (identical scalars), the inner-derivative transmutation operator $\mathcal{L}_0$
   takes the purely elementary form
$$
\bigl(\operatorname{transmuteOpInner} f\bigr)(w) =
  \frac{1}{\sqrt{\pi}} \int_0^1 x^{-1/2}(1 - x)^{-1/2}\bigl(1 - x e^{2w}\bigr)^{-1/2} \,
    \mathcal{D}_{\mathrm{inner}}(f, w, x) \, dx,
$$
   where $\mathcal{D}_{\mathrm{inner}}(f, w, x)$ (`transmuteInnerDiff`) only involves the first and
   second derivatives of $f$ at $w + \log x$. Consequently:
   - `transmuteOpInner` annihilates constant functions identically (`transmuteOpInner_const`),
     eliminating the $s$-channel identity contribution $1$ prior to integration.
   - `transmuteInnerDiff` is related to the radial Euler operator
     $\mathscr{D}_w = \frac{1 + e^w}{1 - e^w} \partial_w$ (`eulerD`) by the exact algebraic
     identity `transmuteInnerDiff_eq_eulerD`.

2. **Modulus and Low-$x$ Bounds for `transmuteInnerKernel` and `transmuteInnerDiff`**:
   - Exact norm formula `norm_transmuteInnerKernel_eq` on `UcDisk × Ioo 0 1`.
   - On the low-$x$ interval $x \in (0, 1/2]$, uniform lower/upper bounds on
     $\|1 \mp x e^w\|$ and $\|1 - x e^{2w}\|$, yielding
     `‖transmuteInnerKernel w x‖ ≤ Real.sqrt 2 * x ^ (-1 / 2) * (1 - x) ^ (-1 / 2)`.

3. **Elementary Beta Tail Integral Bound $I_N(e)$ (`integral_rpow_neg_half_mul_add_rpow_le`)**:
   For $e \in (0, 1]$ and any exponent $\beta \ne 0$, a dyadic split at $\min(e, 1/2)$ gives
   $$\int_0^{1/2} y^{-1/2} (e + y)^{-1/2 - \beta} \, dy \le C \bigl(e^{-\beta} + 1\bigr).$$

4. **High-$x$ Endpoint Cancellation, Cauchy Reductions, and Folded $\theta$-Contour Bound**:
   - On $x \in [1/2, 1)$, the factor $(1 - e^w)^2$ in `transmuteInnerDiff` cancels two inverse
     powers of $\|1 - x e^w\| \ge \frac{1}{3}(\|1 - e^w\| + 1 - x)$
     (`norm_transmuteInnerKernel_mul_diff_le_of_source_bound`).
   - Combining low-$x$ and high-$x$ Cauchy derivative estimates yields the folded $\theta$-contour
     integral bound `norm_folded_integral_transmuteOpInner_le`.

5. **Action of `transmuteOpInner` on `block1d H` for All $H \ge 0$ (`transmuteOpInner_block1d`)**:
   Proves that for all $H \ge 0$ and $w \in \operatorname{UcDisk}$,
$$
\bigl(\operatorname{transmuteOpInner}(\operatorname{block1d} H)\bigr)(w)
  = \operatorname{transmuteWeight}(H) \, e^{H w}.
$$
-/

open MeasureTheory Set Filter Metric Real Complex Topology
open scoped BigOperators ENNReal

/-! ## Section 1: Inner-Derivative Transmutation Operator -/

/-- The radial Euler differential operator $\mathscr{D} f(w) = \frac{1 + e^w}{1 - e^w} f'(w)$. -/
noncomputable def eulerD (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  (1 + Complex.exp w) / (1 - Complex.exp w) * deriv f w

/-- The inner-derivative transmutation kernel at $\delta = 0$:
$$K_{\mathrm{inner}}(w, x) = x^{-1/2} (1 - x)^{-1/2} \bigl(1 - x e^{2w}\bigr)^{-1/2}.$$ -/
noncomputable def transmuteInnerKernel (w : ℂ) (x : ℝ) : ℂ :=
  ((x ^ (-1 / 2 : ℝ) * (1 - x) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
    (1 - (x : ℂ) * Complex.exp (2 * w)) ^ (-1 / 2 : ℂ)

/-- The inner-derivative differential expression at $\delta = 0$:
$$
\mathcal{D}_{\mathrm{inner}}(f, w, x) =
  (1 - e^w)^2 \left[\frac{1 + x e^w}{1 - x e^w} f''(w + \log x)
    + \frac{2 x e^w}{(1 - x e^w)^2} f'(w + \log x)\right]
  - \frac{1}{2}(1 + e^w)^2 f'(w + \log x).
$$ -/
noncomputable def transmuteInnerDiff (f : ℂ → ℂ) (w : ℂ) (x : ℝ) : ℂ :=
  (1 - Complex.exp w) ^ 2 *
    ((1 + (x : ℂ) * Complex.exp w) / (1 - (x : ℂ) * Complex.exp w) *
      deriv (deriv f) (w + (Real.log x : ℂ)) +
      (2 * (x : ℂ) * Complex.exp w) / (1 - (x : ℂ) * Complex.exp w) ^ 2 *
        deriv f (w + (Real.log x : ℂ))) -
    (1 / 2 : ℂ) * (1 + Complex.exp w) ^ 2 * deriv f (w + (Real.log x : ℂ))

/-- The convergent inner-derivative 1D transmutation operator at $\delta = 0$:
$$
\bigl(\operatorname{transmuteOpInner} f\bigr)(w) =
  \frac{1}{\sqrt{\pi}} \int_{x \in (0, 1)}
    \operatorname{transmuteInnerKernel}(w, x) \,
    \operatorname{transmuteInnerDiff}(f, w, x) \, dx.
$$ -/
noncomputable def transmuteOpInner (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  ((Real.sqrt π : ℝ) : ℂ)⁻¹ *
    ∫ x in Ioo (0 : ℝ) 1, transmuteInnerKernel w x * transmuteInnerDiff f w x

/-- `eulerD` of a constant function is identically zero. -/
@[simp]
theorem eulerD_const (c : ℂ) (w : ℂ) : eulerD (fun _ => c) w = 0 := by
  simp [eulerD]

/-- `transmuteInnerDiff` of a constant function is identically zero. -/
@[simp]
theorem transmuteInnerDiff_const (c : ℂ) (w : ℂ) (x : ℝ) :
    transmuteInnerDiff (fun _ => c) w x = 0 := by
  have hd1 : deriv (fun _ : ℂ => c) = fun _ => 0 := by
    ext z; exact deriv_const z c
  simp [transmuteInnerDiff, hd1]

/-- `transmuteOpInner` annihilates constant functions (in particular, the $s$-channel identity $1$)
identically. -/
@[simp]
theorem transmuteOpInner_const (c : ℂ) (w : ℂ) :
    transmuteOpInner (fun _ => c) w = 0 := by
  simp [transmuteOpInner]

/-- Scalar linearity of `transmuteInnerDiff`. -/
theorem transmuteInnerDiff_const_mul (c : ℂ) (f : ℂ → ℂ) (w : ℂ) (x : ℝ) :
    transmuteInnerDiff (fun z => c * f z) w x = c * transmuteInnerDiff f w x := by
  have hd1 : deriv (fun z => c * f z) = fun z => c * deriv f z := by
    ext z; exact deriv_const_mul_field c
  have hd2 : deriv (fun z => c * deriv f z) = fun z => c * deriv (deriv f) z := by
    ext z; exact deriv_const_mul_field c
  dsimp [transmuteInnerDiff]
  rw [hd1, hd2]
  ring

/-- Additivity of `transmuteInnerDiff` for twice-differentiable functions. -/
theorem transmuteInnerDiff_add {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hf' : Differentiable ℂ (deriv f))
    (hg' : Differentiable ℂ (deriv g)) (w : ℂ) (x : ℝ) :
    transmuteInnerDiff (fun z => f z + g z) w x =
      transmuteInnerDiff f w x + transmuteInnerDiff g w x := by
  have hd1 : deriv (fun z => f z + g z) = fun z => deriv f z + deriv g z := by
    ext z; exact deriv_add (hf z) (hg z)
  have hd2 : deriv (fun z => deriv f z + deriv g z) =
      fun z => deriv (deriv f) z + deriv (deriv g) z := by
    ext z; exact deriv_add (hf' z) (hg' z)
  dsimp [transmuteInnerDiff]
  rw [hd1, hd2]
  ring

/-- Subtraction linearity of `transmuteInnerDiff` for twice-differentiable functions. -/
theorem transmuteInnerDiff_sub {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hf' : Differentiable ℂ (deriv f))
    (hg' : Differentiable ℂ (deriv g)) (w : ℂ) (x : ℝ) :
    transmuteInnerDiff (fun z => f z - g z) w x =
      transmuteInnerDiff f w x - transmuteInnerDiff g w x := by
  have hd1 : deriv (fun z => f z - g z) = fun z => deriv f z - deriv g z := by
    ext z; exact deriv_sub (hf z) (hg z)
  have hd2 : deriv (fun z => deriv f z - deriv g z) =
      fun z => deriv (deriv f) z - deriv (deriv g) z := by
    ext z; exact deriv_sub (hf' z) (hg' z)
  dsimp [transmuteInnerDiff]
  rw [hd1, hd2]
  ring

/-- For $w \in \operatorname{UcDisk}$ and $x \in (0, 1)$, $\|x e^w\| < 1$. -/
lemma norm_mul_exp_lt_one {w : ℂ} (hw : w ∈ UcDisk) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ‖(x : ℂ) * Complex.exp w‖ < 1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hx.1.le, Complex.norm_exp]
  have hexp : Real.exp w.re < 1 := Real.exp_lt_one_iff.mpr (mem_UcDisk_iff.mp hw)
  nlinarith [hx.1, hx.2, Real.exp_pos w.re]

lemma one_sub_mul_exp_ne_zero {w : ℂ} (hw : w ∈ UcDisk) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    1 - (x : ℂ) * Complex.exp w ≠ 0 := by
  intro h
  have h1 : (1 : ℂ) = (x : ℂ) * Complex.exp w := sub_eq_zero.mp h
  have h2 : (1 : ℝ) = ‖(x : ℂ) * Complex.exp w‖ := by
    simpa using congrArg norm h1
  linarith [norm_mul_exp_lt_one hw hx]

lemma one_add_mul_exp_ne_zero {w : ℂ} (hw : w ∈ UcDisk) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    1 + (x : ℂ) * Complex.exp w ≠ 0 := by
  intro h
  have h1 : (x : ℂ) * Complex.exp w = -1 := eq_neg_of_add_eq_zero_right h
  have h2 : ‖(x : ℂ) * Complex.exp w‖ = 1 := by
    simpa using congrArg norm h1
  linarith [norm_mul_exp_lt_one hw hx]

/-- Derivative of the Euler prefactor $z \mapsto \frac{1 + e^z}{1 - e^z}$ at any point where
$1 - e^z \ne 0$. -/
lemma hasDerivAt_one_add_exp_div_one_sub_exp {z : ℂ} (hz : 1 - Complex.exp z ≠ 0) :
    HasDerivAt (fun u : ℂ => (1 + Complex.exp u) / (1 - Complex.exp u))
      (2 * Complex.exp z / (1 - Complex.exp z) ^ 2) z := by
  have h1 : HasDerivAt (fun u : ℂ => 1 + Complex.exp u) (Complex.exp z) z := by
    convert (hasDerivAt_const z (1 : ℂ)).add (Complex.hasDerivAt_exp z) using 1
    ring
  have h2 : HasDerivAt (fun u : ℂ => 1 - Complex.exp u) (-Complex.exp z) z := by
    convert (hasDerivAt_const z (1 : ℂ)).sub (Complex.hasDerivAt_exp z) using 1
    ring
  convert h1.div h2 hz using 1
  ring

/-- Derivative of `eulerD f` at any point $z$ where $1 - e^z \ne 0$. -/
lemma deriv_eulerD {f : ℂ → ℂ} (hf' : Differentiable ℂ (deriv f)) {z : ℂ}
    (hz : 1 - Complex.exp z ≠ 0) :
    deriv (eulerD f) z =
      (1 + Complex.exp z) / (1 - Complex.exp z) * deriv (deriv f) z +
        (2 * Complex.exp z) / (1 - Complex.exp z) ^ 2 * deriv f z := by
  have hd_pref := hasDerivAt_one_add_exp_div_one_sub_exp hz
  have hd_prod : HasDerivAt (eulerD f)
      (2 * Complex.exp z / (1 - Complex.exp z) ^ 2 * deriv f z +
        (1 + Complex.exp z) / (1 - Complex.exp z) * deriv (deriv f) z) z :=
    hd_pref.mul (hf' z).hasDerivAt
  rw [hd_prod.deriv]
  ring

/-- Exact algebraic connection between `transmuteInnerDiff` and the radial Euler operator
`eulerD` ($\mathscr{D}$): for any twice-differentiable $f : \mathbb{C} \to \mathbb{C}$,
$w \in \operatorname{UcDisk}$, and $x \in (0, 1)$,
$$
\operatorname{transmuteInnerDiff}(f, w, x) =
  \frac{1 - x e^w}{1 + x e^w} \left[(1 - e^w)^2 (\mathscr{D}^2 f)(w + \log x)
    - \frac{1}{2}(1 + e^w)^2 (\mathscr{D} f)(w + \log x)\right].
$$ -/
theorem transmuteInnerDiff_eq_eulerD {f : ℂ → ℂ} (_hf : Differentiable ℂ f)
    (hf' : Differentiable ℂ (deriv f)) {w : ℂ} (hw : w ∈ UcDisk)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    transmuteInnerDiff f w x =
      ((1 - (x : ℂ) * Complex.exp w) / (1 + (x : ℂ) * Complex.exp w)) *
        ((1 - Complex.exp w) ^ 2 * eulerD (eulerD f) (w + (Real.log x : ℂ)) -
          (1 / 2 : ℂ) * (1 + Complex.exp w) ^ 2 * eulerD f (w + (Real.log x : ℂ))) := by
  set z : ℂ := w + (Real.log x : ℂ)
  have hexp_z : Complex.exp z = (x : ℂ) * Complex.exp w := by
    dsimp [z]
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hx.1, mul_comm]
  have hz_sub : 1 - Complex.exp z ≠ 0 := by
    rw [hexp_z]
    exact one_sub_mul_exp_ne_zero hw hx
  have hz_add : 1 + Complex.exp z ≠ 0 := by
    rw [hexp_z]
    exact one_add_mul_exp_ne_zero hw hx
  have hd_euler := deriv_eulerD hf' hz_sub
  have h_cancel :
      ((1 - (x : ℂ) * Complex.exp w) / (1 + (x : ℂ) * Complex.exp w)) *
        ((1 - Complex.exp w) ^ 2 * eulerD (eulerD f) z -
          (1 / 2 : ℂ) * (1 + Complex.exp w) ^ 2 * eulerD f z) =
      (1 - Complex.exp w) ^ 2 * deriv (eulerD f) z -
        (1 / 2 : ℂ) * (1 + Complex.exp w) ^ 2 * deriv f z := by
    dsimp [eulerD]
    rw [hexp_z] at hz_sub hz_add ⊢
    field_simp [hz_sub, hz_add]
  change transmuteInnerDiff f w x =
    ((1 - (x : ℂ) * Complex.exp w) / (1 + (x : ℂ) * Complex.exp w)) *
      ((1 - Complex.exp w) ^ 2 * eulerD (eulerD f) z -
        (1 / 2 : ℂ) * (1 + Complex.exp w) ^ 2 * eulerD f z)
  rw [h_cancel, hd_euler, hexp_z]
  dsimp [transmuteInnerDiff, z]
  ring

/-! ## Section 2: Modulus & Low-$x$ Endpoint Bounds -/

/-- Exact modulus of `transmuteInnerKernel w x` for $w \in \operatorname{UcDisk}$ and
$x \in (0, 1)$. -/
theorem norm_transmuteInnerKernel_eq {w : ℂ} (hw : w ∈ UcDisk)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ‖transmuteInnerKernel w x‖ =
      x ^ (-1 / 2 : ℝ) * (1 - x) ^ (-1 / 2 : ℝ) *
        ‖1 - (x : ℂ) * Complex.exp (2 * w)‖ ^ (-1 / 2 : ℝ) := by
  dsimp [transmuteInnerKernel]
  have hx0 : 0 < x := hx.1
  have hx1 : 0 < 1 - x := sub_pos.mpr hx.2
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h_lt1 : ‖(x : ℂ) * Complex.exp (2 * w)‖ < 1 :=
    norm_mul_exp_two_mul_lt_one hw hx
  have hz_ne : 1 - (x : ℂ) * Complex.exp (2 * w) ≠ 0 := by
    intro h
    have h1 : (1 : ℂ) = (x : ℂ) * Complex.exp (2 * w) := sub_eq_zero.mp h
    have h2 : (1 : ℝ) = ‖(x : ℂ) * Complex.exp (2 * w)‖ := by
      simpa using congrArg norm h1
    linarith
  have hcpow :
      ‖(1 - (x : ℂ) * Complex.exp (2 * w)) ^ (-1 / 2 : ℂ)‖ =
        ‖1 - (x : ℂ) * Complex.exp (2 * w)‖ ^ (-1 / 2 : ℝ) := by
    rw [cpow_def_of_ne_zero hz_ne, Complex.norm_exp]
    have hre : (Complex.log (1 - (x : ℂ) * Complex.exp (2 * w)) * (-1 / 2 : ℂ)).re =
        Real.log ‖1 - (x : ℂ) * Complex.exp (2 * w)‖ * (-1 / 2 : ℝ) := by
      simp [Complex.mul_re, Complex.log_re]
    rw [hre, Real.rpow_def_of_pos (norm_pos_iff.mpr hz_ne)]
  rw [hcpow]

/-- For $w \in \operatorname{UcDisk}$ and $x \in (0, 1/2]$, $\|x e^w\| \le 1/2$. -/
lemma norm_mul_exp_le_half {w : ℂ} (hw : w ∈ UcDisk) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) (1 / 2)) :
    ‖(x : ℂ) * Complex.exp w‖ ≤ 1 / 2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hx.1.le, Complex.norm_exp]
  have hexp : Real.exp w.re ≤ 1 := Real.exp_le_one_iff.mpr (mem_UcDisk_iff.mp hw).le
  calc
    x * Real.exp w.re ≤ (1 / 2) * 1 :=
      mul_le_mul hx.2 hexp (Real.exp_pos w.re).le (by norm_num)
    _ = 1 / 2 := mul_one _

/-- For $w \in \operatorname{UcDisk}$ and $x \in (0, 1/2]$,
$1/2 \le \|1 - x e^w\|$. -/
theorem half_le_norm_one_sub_mul_exp {w : ℂ} (hw : w ∈ UcDisk)
    {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) (1 / 2)) :
    1 / 2 ≤ ‖1 - (x : ℂ) * Complex.exp w‖ := by
  have h1 := norm_mul_exp_le_half hw hx
  have h2 := norm_sub_norm_le (1 : ℂ) ((x : ℂ) * Complex.exp w)
  rw [norm_one] at h2
  linarith

/-- For $w \in \operatorname{UcDisk}$ and $x \in (0, 1/2]$,
$\|1 + x e^w\| \le 2$. -/
theorem norm_one_add_mul_exp_le_two {w : ℂ} (hw : w ∈ UcDisk)
    {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) (1 / 2)) :
    ‖1 + (x : ℂ) * Complex.exp w‖ ≤ 2 := by
  have h1 := norm_mul_exp_le_half hw hx
  have h2 := norm_add_le (1 : ℂ) ((x : ℂ) * Complex.exp w)
  rw [norm_one] at h2
  linarith

/-- For $w \in \operatorname{UcDisk}$ and $x \in (0, 1/2]$,
$1/2 \le \|1 - x e^{2w}\|$. -/
theorem half_le_norm_one_sub_mul_exp_two_mul {w : ℂ} (hw : w ∈ UcDisk)
    {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) (1 / 2)) :
    1 / 2 ≤ ‖1 - (x : ℂ) * Complex.exp (2 * w)‖ := by
  have hw2 : 2 * w ∈ UcDisk := by
    have hre : (2 * w).re = 2 * w.re := by simp [Complex.mul_re]
    rw [mem_UcDisk_iff, hre]
    linarith [mem_UcDisk_iff.mp hw]
  exact half_le_norm_one_sub_mul_exp hw2 hx

/-- On the low-$x$ interval $x \in (0, 1/2]$, `transmuteInnerKernel w x` is uniformly bounded by
$\sqrt{2} \, x^{-1/2} (1 - x)^{-1/2}$ for all $w \in \operatorname{UcDisk}$. -/
theorem norm_transmuteInnerKernel_le {w : ℂ} (hw : w ∈ UcDisk)
    {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) (1 / 2)) :
    ‖transmuteInnerKernel w x‖ ≤
      Real.sqrt 2 * x ^ (-1 / 2 : ℝ) * (1 - x) ^ (-1 / 2 : ℝ) := by
  have hx_ioo : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, by linarith [hx.2]⟩
  rw [norm_transmuteInnerKernel_eq hw hx_ioo]
  have hx0 : 0 < x := hx.1
  have hx1 : 0 < 1 - x := sub_pos.mpr hx_ioo.2
  have h_ge : 1 / 2 ≤ ‖1 - (x : ℂ) * Complex.exp (2 * w)‖ :=
    half_le_norm_one_sub_mul_exp_two_mul hw hx
  have h_rpow_le :
      ‖1 - (x : ℂ) * Complex.exp (2 * w)‖ ^ (-1 / 2 : ℝ) ≤ Real.sqrt 2 := by
    have h_step :
        ‖1 - (x : ℂ) * Complex.exp (2 * w)‖ ^ (-1 / 2 : ℝ) ≤
          (1 / 2 : ℝ) ^ (-1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) h_ge (by norm_num)
    have h_sqrt : (1 / 2 : ℝ) ^ (-1 / 2 : ℝ) = Real.sqrt 2 := by
      have h1 : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := one_div 2
      have h2 : (-1 / 2 : ℝ) = - (1 / 2 : ℝ) := by ring
      rw [h1, h2, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num),
        inv_inv, ← Real.sqrt_eq_rpow]
    rwa [h_sqrt] at h_step
  calc
    x ^ (-1 / 2 : ℝ) * (1 - x) ^ (-1 / 2 : ℝ) *
        ‖1 - (x : ℂ) * Complex.exp (2 * w)‖ ^ (-1 / 2 : ℝ)
      ≤ x ^ (-1 / 2 : ℝ) * (1 - x) ^ (-1 / 2 : ℝ) * Real.sqrt 2 :=
        mul_le_mul_of_nonneg_left h_rpow_le (by positivity)
    _ = Real.sqrt 2 * x ^ (-1 / 2 : ℝ) * (1 - x) ^ (-1 / 2 : ℝ) := by ring

/-- On the low-$x$ interval $x \in (0, 1/2]$, `transmuteInnerDiff f w x` is uniformly bounded in
terms of the first and second derivatives of $f$ at $w + \log x$ for all
$w \in \operatorname{UcDisk}$:
$$
\|\operatorname{transmuteInnerDiff}(f, w, x)\| \le
  16 \, \|f''(w + \log x)\| + 18 \, \|f'(w + \log x)\|.
$$ -/
theorem norm_transmuteInnerDiff_le (f : ℂ → ℂ) {w : ℂ} (hw : w ∈ UcDisk)
    {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) (1 / 2)) :
    ‖transmuteInnerDiff f w x‖ ≤
      16 * ‖deriv (deriv f) (w + (Real.log x : ℂ))‖ +
        18 * ‖deriv f (w + (Real.log x : ℂ))‖ := by
  dsimp [transmuteInnerDiff]
  set z : ℂ := w + (Real.log x : ℂ)
  have hexp_le1 : ‖Complex.exp w‖ ≤ 1 := by
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    exact (mem_UcDisk_iff.mp hw).le
  have h1_sub_le2 : ‖1 - Complex.exp w‖ ≤ 2 := by
    have h := norm_sub_le (1 : ℂ) (Complex.exp w)
    rw [norm_one] at h
    linarith
  have h1_add_le2 : ‖1 + Complex.exp w‖ ≤ 2 := by
    have h := norm_add_le (1 : ℂ) (Complex.exp w)
    rw [norm_one] at h
    linarith
  have h1_sub_sq : ‖(1 - Complex.exp w) ^ 2‖ ≤ 4 := by
    rw [norm_pow]
    nlinarith [norm_nonneg (1 - Complex.exp w)]
  have h1_add_sq : ‖(1 + Complex.exp w) ^ 2‖ ≤ 4 := by
    rw [norm_pow]
    nlinarith [norm_nonneg (1 + Complex.exp w)]
  have hv_le : ‖(x : ℂ) * Complex.exp w‖ ≤ 1 / 2 := norm_mul_exp_le_half hw hx
  have h_sub_ge : 1 / 2 ≤ ‖1 - (x : ℂ) * Complex.exp w‖ :=
    half_le_norm_one_sub_mul_exp hw hx
  have h_add_le : ‖1 + (x : ℂ) * Complex.exp w‖ ≤ 2 :=
    norm_one_add_mul_exp_le_two hw hx
  have h_quot1 : ‖(1 + (x : ℂ) * Complex.exp w) / (1 - (x : ℂ) * Complex.exp w)‖ ≤ 4 := by
    rw [norm_div, div_le_iff₀ (by linarith)]
    linarith
  have h_quot2 : ‖(2 * (x : ℂ) * Complex.exp w) / (1 - (x : ℂ) * Complex.exp w) ^ 2‖ ≤ 4 := by
    have h_sq_ge : 1 / 4 ≤ ‖1 - (x : ℂ) * Complex.exp w‖ ^ 2 := by
      nlinarith
    have h_num_le : ‖2 * (x : ℂ) * Complex.exp w‖ ≤ 1 := by
      rw [mul_assoc, norm_mul, Complex.norm_ofNat]
      linarith
    rw [norm_div, norm_pow, div_le_iff₀ (by linarith)]
    linarith
  have h_inner_le :
      ‖(1 + (x : ℂ) * Complex.exp w) / (1 - (x : ℂ) * Complex.exp w) * deriv (deriv f) z +
        (2 * (x : ℂ) * Complex.exp w) / (1 - (x : ℂ) * Complex.exp w) ^ 2 * deriv f z‖ ≤
      4 * ‖deriv (deriv f) z‖ + 4 * ‖deriv f z‖ := by
    calc
      ‖(1 + (x : ℂ) * Complex.exp w) / (1 - (x : ℂ) * Complex.exp w) * deriv (deriv f) z +
        (2 * (x : ℂ) * Complex.exp w) / (1 - (x : ℂ) * Complex.exp w) ^ 2 * deriv f z‖
        ≤ ‖(1 + (x : ℂ) * Complex.exp w) / (1 - (x : ℂ) * Complex.exp w) * deriv (deriv f) z‖ +
            ‖(2 * (x : ℂ) * Complex.exp w) / (1 - (x : ℂ) * Complex.exp w) ^ 2 * deriv f z‖ :=
          norm_add_le _ _
      _ = ‖(1 + (x : ℂ) * Complex.exp w) / (1 - (x : ℂ) * Complex.exp w)‖ * ‖deriv (deriv f) z‖ +
            ‖(2 * (x : ℂ) * Complex.exp w) / (1 - (x : ℂ) * Complex.exp w) ^ 2‖ * ‖deriv f z‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ 4 * ‖deriv (deriv f) z‖ + 4 * ‖deriv f z‖ :=
          add_le_add
            (mul_le_mul_of_nonneg_right h_quot1 (norm_nonneg _))
            (mul_le_mul_of_nonneg_right h_quot2 (norm_nonneg _))
  have h_term1 :
      ‖(1 - Complex.exp w) ^ 2 *
        ((1 + (x : ℂ) * Complex.exp w) / (1 - (x : ℂ) * Complex.exp w) * deriv (deriv f) z +
          (2 * (x : ℂ) * Complex.exp w) / (1 - (x : ℂ) * Complex.exp w) ^ 2 * deriv f z)‖ ≤
      4 * (4 * ‖deriv (deriv f) z‖ + 4 * ‖deriv f z‖) := by
    rw [norm_mul]
    exact mul_le_mul h1_sub_sq h_inner_le (norm_nonneg _) (by norm_num)
  have h_term2 :
      ‖(1 / 2 : ℂ) * (1 + Complex.exp w) ^ 2 * deriv f z‖ ≤ 2 * ‖deriv f z‖ := by
    rw [norm_mul, norm_mul, norm_div, norm_one, Complex.norm_ofNat]
    have : 1 / 2 * ‖(1 + Complex.exp w) ^ 2‖ ≤ 2 := by linarith
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  have h_sub := norm_sub_le
    ((1 - Complex.exp w) ^ 2 *
      ((1 + (x : ℂ) * Complex.exp w) / (1 - (x : ℂ) * Complex.exp w) * deriv (deriv f) z +
        (2 * (x : ℂ) * Complex.exp w) / (1 - (x : ℂ) * Complex.exp w) ^ 2 * deriv f z))
    ((1 / 2 : ℂ) * (1 + Complex.exp w) ^ 2 * deriv f z)
  linarith

/-! ## Section 3: Elementary Beta Tail Integral Bound $I_N(e)$ -/

/-- Pointwise upper bound on $(e + y)^\alpha$ when $0 < a \le e + y \le 2 a$:
$$(e + y)^\alpha \le \max\bigl(1,\, 2^\alpha\bigr) \, a^\alpha.$$ -/
lemma add_rpow_le_max_mul_rpow {a y e α : ℝ} (ha : 0 < a)
    (h_lo : a ≤ e + y) (h_hi : e + y ≤ 2 * a) :
    (e + y) ^ α ≤ max 1 ((2 : ℝ) ^ α) * a ^ α := by
  rcases le_or_gt α 0 with hα | hα
  · calc
      (e + y) ^ α ≤ a ^ α := Real.rpow_le_rpow_of_nonpos ha h_lo hα
      _ = 1 * a ^ α := (one_mul _).symm
      _ ≤ max 1 ((2 : ℝ) ^ α) * a ^ α :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · calc
      (e + y) ^ α ≤ (2 * a) ^ α :=
        Real.rpow_le_rpow (by linarith) h_hi hα.le
      _ = (2 : ℝ) ^ α * a ^ α := Real.mul_rpow (by norm_num) ha.le
      _ ≤ max 1 ((2 : ℝ) ^ α) * a ^ α :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- Integrability of $y \mapsto y^{-1/2} (e + y)^\alpha$ on $[a, b]$ for $0 \le a \le b$ and
$e > 0$. -/
lemma intervalIntegrable_rpow_neg_half_mul_add_rpow {a b e : ℝ} (α : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (he : 0 < e) :
    IntervalIntegrable (fun y : ℝ => y ^ (-1 / 2 : ℝ) * (e + y) ^ α) volume a b := by
  have h1 : IntervalIntegrable (fun y : ℝ => y ^ (-1 / 2 : ℝ)) volume a b :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have h2 : ContinuousOn (fun y : ℝ => (e + y) ^ α) (uIcc a b) := by
    rw [uIcc_of_le hab]
    intro y hy
    refine ContinuousAt.continuousWithinAt ?_
    refine (continuousAt_const.add continuousAt_id).rpow_const (Or.inl ?_)
    dsimp
    linarith [hy.1]
  exact h1.mul_continuousOn h2

/-- **Elementary Beta Tail Integral Bound $I_N(e)$**:
For any $\beta \ne 0$, there exists $C \ge 0$ such that for all $e \in (0, 1]$,
$$\int_0^{1/2} y^{-1/2} (e + y)^{-1/2 - \beta} \, dy \le C \bigl(e^{-\beta} + 1\bigr).$$ -/
theorem integral_rpow_neg_half_mul_add_rpow_le {β : ℝ} (hβ : β ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {e : ℝ}, 0 < e → e ≤ 1 →
      (∫ y in (0 : ℝ)..(1 / 2), y ^ (-1 / 2 : ℝ) * (e + y) ^ (-1 / 2 - β)) ≤
        C * (e ^ (-β) + 1) := by
  set α : ℝ := -1 / 2 - β
  set M : ℝ := max 1 ((2 : ℝ) ^ α)
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left 1 ((2 : ℝ) ^ α))
  have hβ_abs_pos : 0 < |β| := abs_pos.mpr hβ
  set C : ℝ := 2 * M + M * ((1 / 2 : ℝ) ^ (-β) + 1) / |β|
  refine ⟨C, by positivity, fun {e} he_pos _he_le => ?_⟩
  set e0 : ℝ := min e (1 / 2)
  have he0_pos : 0 < e0 := lt_min he_pos (by norm_num)
  have he0_le_e : e0 ≤ e := min_le_left e (1 / 2)
  have he0_le_half : e0 ≤ 1 / 2 := min_le_right e (1 / 2)
  have h_int1 : IntervalIntegrable
      (fun y : ℝ => y ^ (-1 / 2 : ℝ) * (e + y) ^ α) volume 0 e0 :=
    intervalIntegrable_rpow_neg_half_mul_add_rpow α le_rfl he0_pos.le he_pos
  have h_int2 : IntervalIntegrable
      (fun y : ℝ => y ^ (-1 / 2 : ℝ) * (e + y) ^ α) volume e0 (1 / 2) :=
    intervalIntegrable_rpow_neg_half_mul_add_rpow α he0_pos.le he0_le_half he_pos
  have h_split := (intervalIntegral.integral_add_adjacent_intervals h_int1 h_int2).symm
  -- Part 1: bound on [0, e0]
  have h_part1 :
      (∫ y in (0 : ℝ)..e0, y ^ (-1 / 2 : ℝ) * (e + y) ^ α) ≤
        2 * M * e ^ (-β) := by
    have h_rhs_int : IntervalIntegrable
        (fun y : ℝ => (M * e ^ α) * y ^ (-1 / 2 : ℝ)) volume 0 e0 :=
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul (M * e ^ α)
    have h_mono :
        (∫ y in (0 : ℝ)..e0, y ^ (-1 / 2 : ℝ) * (e + y) ^ α) ≤
          ∫ y in (0 : ℝ)..e0, (M * e ^ α) * y ^ (-1 / 2 : ℝ) := by
      refine intervalIntegral.integral_mono_on he0_pos.le h_int1 h_rhs_int fun y hy => ?_
      have hy0 : 0 ≤ y := hy.1
      have hye : y ≤ e := hy.2.trans he0_le_e
      have h_add_le : (e + y) ^ α ≤ M * e ^ α :=
        add_rpow_le_max_mul_rpow he_pos (by linarith) (by linarith)
      calc
        y ^ (-1 / 2 : ℝ) * (e + y) ^ α
          ≤ y ^ (-1 / 2 : ℝ) * (M * e ^ α) :=
            mul_le_mul_of_nonneg_left h_add_le (Real.rpow_nonneg hy0 _)
        _ = (M * e ^ α) * y ^ (-1 / 2 : ℝ) := by ring
    rw [intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -1 / 2))] at h_mono
    have h_exp_half : (-1 / 2 : ℝ) + 1 = 1 / 2 := by ring
    rw [h_exp_half, Real.zero_rpow (by norm_num)] at h_mono
    have he0_rpow_le : e0 ^ (1 / 2 : ℝ) ≤ e ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow he0_pos.le he0_le_e (by norm_num)
    have h_eval_le :
        (M * e ^ α) * ((e0 ^ (1 / 2 : ℝ) - 0) / (1 / 2 : ℝ)) ≤
          2 * M * (e ^ α * e ^ (1 / 2 : ℝ)) := by
      calc
        (M * e ^ α) * ((e0 ^ (1 / 2 : ℝ) - 0) / (1 / 2 : ℝ))
          = 2 * M * e ^ α * e0 ^ (1 / 2 : ℝ) := by ring
        _ ≤ 2 * M * e ^ α * e ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left he0_rpow_le (by positivity)
        _ = 2 * M * (e ^ α * e ^ (1 / 2 : ℝ)) := by ring
    have h_rpow_comb : e ^ α * e ^ (1 / 2 : ℝ) = e ^ (-β) := by
      rw [← Real.rpow_add he_pos]
      congr 1
      dsimp [α]
      ring
    rw [h_rpow_comb] at h_eval_le
    exact h_mono.trans h_eval_le
  -- Part 2: bound on [e0, 1/2]
  have h_part2 :
      (∫ y in e0..(1 / 2), y ^ (-1 / 2 : ℝ) * (e + y) ^ α) ≤
        (M * ((1 / 2 : ℝ) ^ (-β) + 1) / |β|) * (e ^ (-β) + 1) := by
    rcases le_or_gt (1 / 2 : ℝ) e with h_ge | h_lt
    · have he0_eq : e0 = 1 / 2 := min_eq_right h_ge
      rw [he0_eq, intervalIntegral.integral_same]
      positivity
    · have he0_eq : e0 = e := min_eq_left h_lt.le
      rw [he0_eq]
      rw [he0_eq] at h_int2
      have h_rhs_cont : ContinuousOn (fun y : ℝ => M * y ^ (-1 - β)) (uIcc e (1 / 2)) := by
        rw [uIcc_of_le h_lt.le]
        intro y hy
        exact continuousAt_const.continuousWithinAt.mul
          (continuousAt_id.rpow_const (Or.inl (by dsimp; linarith [hy.1]))).continuousWithinAt
      have h_mono :
          (∫ y in e..(1 / 2), y ^ (-1 / 2 : ℝ) * (e + y) ^ α) ≤
            ∫ y in e..(1 / 2), M * y ^ (-1 - β) := by
        refine intervalIntegral.integral_mono_on h_lt.le h_int2
          (h_rhs_cont.intervalIntegrable) fun y hy => ?_
        have hy_pos : 0 < y := lt_of_lt_of_le he_pos hy.1
        have h_add_le : (e + y) ^ α ≤ M * y ^ α :=
          add_rpow_le_max_mul_rpow hy_pos (by linarith) (by linarith [hy.1])
        calc
          y ^ (-1 / 2 : ℝ) * (e + y) ^ α
            ≤ y ^ (-1 / 2 : ℝ) * (M * y ^ α) :=
              mul_le_mul_of_nonneg_left h_add_le (by positivity)
          _ = M * (y ^ (-1 / 2 : ℝ) * y ^ α) := by ring
          _ = M * y ^ (-1 - β) := by
            rw [← Real.rpow_add hy_pos]
            congr 2
            dsimp [α]
            ring
      have h_ne_neg1 : -1 - β ≠ -1 := by intro h; apply hβ; linarith
      have h_zero_not_mem : (0 : ℝ) ∉ uIcc e (1 / 2) := by
        rw [uIcc_of_le h_lt.le]
        intro h0
        linarith [h0.1]
      rw [intervalIntegral.integral_const_mul,
        integral_rpow (Or.inr ⟨h_ne_neg1, h_zero_not_mem⟩)] at h_mono
      have h_exp : -1 - β + 1 = -β := by ring
      rw [h_exp] at h_mono
      have h_quot_le :
          ((1 / 2 : ℝ) ^ (-β) - e ^ (-β)) / (-β) ≤
            ((1 / 2 : ℝ) ^ (-β) + e ^ (-β)) / |β| := by
        calc
          ((1 / 2 : ℝ) ^ (-β) - e ^ (-β)) / (-β)
            ≤ |((1 / 2 : ℝ) ^ (-β) - e ^ (-β)) / (-β)| := le_abs_self _
          _ = |(1 / 2 : ℝ) ^ (-β) - e ^ (-β)| / |β| := by
              rw [abs_div, abs_neg]
          _ ≤ (|(1 / 2 : ℝ) ^ (-β)| + |e ^ (-β)|) / |β| :=
              div_le_div_of_nonneg_right (abs_sub _ _) hβ_abs_pos.le
          _ = ((1 / 2 : ℝ) ^ (-β) + e ^ (-β)) / |β| := by
              rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
      have h_prod_le :
          (1 / 2 : ℝ) ^ (-β) + e ^ (-β) ≤
            ((1 / 2 : ℝ) ^ (-β) + 1) * (e ^ (-β) + 1) := by
        nlinarith [show (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (-β) by positivity,
          show (0 : ℝ) ≤ e ^ (-β) by positivity]
      calc
        (∫ y in e..(1 / 2), y ^ (-1 / 2 : ℝ) * (e + y) ^ α)
          ≤ M * (((1 / 2 : ℝ) ^ (-β) - e ^ (-β)) / (-β)) := h_mono
        _ ≤ M * (((1 / 2 : ℝ) ^ (-β) + e ^ (-β)) / |β|) :=
            mul_le_mul_of_nonneg_left h_quot_le hM_pos.le
        _ ≤ M * ((((1 / 2 : ℝ) ^ (-β) + 1) * (e ^ (-β) + 1)) / |β|) :=
            mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_right h_prod_le hβ_abs_pos.le) hM_pos.le
        _ = (M * ((1 / 2 : ℝ) ^ (-β) + 1) / |β|) * (e ^ (-β) + 1) := by ring
  -- Combine Part 1 and Part 2
  rw [h_split]
  calc
    (∫ y in (0 : ℝ)..e0, y ^ (-1 / 2 : ℝ) * (e + y) ^ α) +
        (∫ y in e0..(1 / 2), y ^ (-1 / 2 : ℝ) * (e + y) ^ α)
      ≤ 2 * M * e ^ (-β) +
          (M * ((1 / 2 : ℝ) ^ (-β) + 1) / |β|) * (e ^ (-β) + 1) :=
        add_le_add h_part1 h_part2
    _ ≤ 2 * M * (e ^ (-β) + 1) +
          (M * ((1 / 2 : ℝ) ^ (-β) + 1) / |β|) * (e ^ (-β) + 1) := by
        refine add_le_add ?_ le_rfl
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = C * (e ^ (-β) + 1) := by dsimp [C]; ring

/-! ## Section 4: High-$x$ Endpoint Geometry and Operator Bounds on $x \in [1/2, 1)$ -/

/-- Exact quadratic decomposition of $\|1 - x q\|^2$:
$$\|1 - x q\|^2 = (1 - x)^2 + 2 x (1 - x) (1 - \operatorname{Re} q) + x^2 \|1 - q\|^2.$$ -/
theorem norm_one_sub_mul_sq_eq (x : ℝ) (q : ℂ) :
    ‖1 - (x : ℂ) * q‖ ^ 2 =
      (1 - x) ^ 2 + 2 * x * (1 - x) * (1 - q.re) + x ^ 2 * ‖1 - q‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
  ring

/-- Upper bound $\|1 - x e^w\| \le \|1 - e^w\| + (1 - x)$ for $x \in [0, 1]$ and
$w \in \mathbb{C}$. -/
theorem norm_one_sub_mul_exp_le (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (w : ℂ) :
    ‖1 - (x : ℂ) * Complex.exp w‖ ≤ ‖1 - Complex.exp w‖ + (1 - x) := by
  have h_decomp :
      1 - (x : ℂ) * Complex.exp w =
        (x : ℂ) * (1 - Complex.exp w) + ((1 - x : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h_decomp]
  calc
    ‖(x : ℂ) * (1 - Complex.exp w) + ((1 - x : ℝ) : ℂ)‖
      ≤ ‖(x : ℂ) * (1 - Complex.exp w)‖ + ‖((1 - x : ℝ) : ℂ)‖ := norm_add_le _ _
    _ = x * ‖1 - Complex.exp w‖ + (1 - x) := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hx.1,
          Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr hx.2)]
    _ ≤ 1 * ‖1 - Complex.exp w‖ + (1 - x) :=
        add_le_add (mul_le_mul_of_nonneg_right hx.2 (norm_nonneg _)) le_rfl
    _ = ‖1 - Complex.exp w‖ + (1 - x) := by ring

/-- Lower bound $\frac{1}{3}\bigl(\|1 - e^w\| + (1 - x)\bigr) \le \|1 - x e^w\|$ for
$w \in \operatorname{UcDisk}$ and $x \in [1/2, 1]$. -/
theorem le_norm_one_sub_mul_exp {w : ℂ} (hw : w ∈ UcDisk)
    {x : ℝ} (hx : x ∈ Icc (1 / 2 : ℝ) 1) :
    (1 / 3 : ℝ) * (‖1 - Complex.exp w‖ + (1 - x)) ≤
      ‖1 - (x : ℂ) * Complex.exp w‖ := by
  set q : ℂ := Complex.exp w
  set a : ℝ := ‖1 - q‖
  set b : ℝ := 1 - x
  have ha_nonneg : 0 ≤ a := norm_nonneg _
  have hb_nonneg : 0 ≤ b := sub_nonneg.mpr hx.2
  have hx_nonneg : 0 ≤ x := by linarith [hx.1]
  have hq_re_le1 : q.re ≤ 1 := by
    calc
      q.re ≤ ‖q‖ := Complex.re_le_norm q
      _ = Real.exp w.re := Complex.norm_exp w
      _ ≤ 1 := Real.exp_le_one_iff.mpr (mem_UcDisk_iff.mp hw).le
  have h_cross_nonneg : 0 ≤ 2 * x * (1 - x) * (1 - q.re) :=
    mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hx_nonneg) hb_nonneg)
      (sub_nonneg.mpr hq_re_le1)
  have hx_sq_ge : (1 / 4 : ℝ) * a ^ 2 ≤ x ^ 2 * a ^ 2 := by
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg a)
    nlinarith [hx.1]
  have h_alg : ((1 / 3 : ℝ) * (a + b)) ^ 2 ≤ b ^ 2 + (1 / 4 : ℝ) * a ^ 2 := by
    have : 0 ≤ (2 * a - 2 * b) ^ 2 + a ^ 2 + 28 * b ^ 2 := by positivity
    linarith
  have h_sq_le : ((1 / 3 : ℝ) * (a + b)) ^ 2 ≤ ‖1 - (x : ℂ) * q‖ ^ 2 := by
    rw [norm_one_sub_mul_sq_eq x q]
    dsimp [a, b] at h_alg hx_sq_ge ⊢
    linarith
  nlinarith [norm_nonneg (1 - (x : ℂ) * q)]

/-- On the half-strip $\operatorname{Im} w \in [-\pi/2, \pi/2]$, $1 \le \|1 + e^w\|$. -/
theorem one_le_norm_one_add_exp {w : ℂ} (him : w.im ∈ Icc (-π / 2) (π / 2)) :
    1 ≤ ‖1 + Complex.exp w‖ := by
  have hcos : 0 ≤ Real.cos w.im :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [him.1], him.2⟩
  have hre : 1 ≤ (1 + Complex.exp w).re := by
    simp only [Complex.add_re, Complex.one_re, Complex.exp_re]
    nlinarith [Real.exp_pos w.re]
  exact hre.trans (Complex.re_le_norm (1 + Complex.exp w))

/-- On the half-strip $\operatorname{Im} w \in [-\pi/2, \pi/2]$,
$\|1 - e^w\| \le \|1 - e^{2w}\|$. -/
theorem norm_one_sub_exp_le_norm_one_sub_exp_two_mul {w : ℂ}
    (him : w.im ∈ Icc (-π / 2) (π / 2)) :
    ‖1 - Complex.exp w‖ ≤ ‖1 - Complex.exp (2 * w)‖ := by
  have h_fac : 1 - Complex.exp (2 * w) = (1 - Complex.exp w) * (1 + Complex.exp w) := by
    have h2w : 2 * w = w + w := two_mul w
    rw [h2w, Complex.exp_add]
    ring
  rw [h_fac, norm_mul]
  calc
    ‖1 - Complex.exp w‖ = ‖1 - Complex.exp w‖ * 1 := (mul_one _).symm
    _ ≤ ‖1 - Complex.exp w‖ * ‖1 + Complex.exp w‖ :=
      mul_le_mul_of_nonneg_left (one_le_norm_one_add_exp him) (norm_nonneg _)

/-- Lower bound $\frac{1}{3}\bigl(\|1 - e^w\| + (1 - x)\bigr) \le \|1 - x e^{2w}\|$ for
$w \in \operatorname{UcDisk}$ with $\operatorname{Im} w \in [-\pi/2, \pi/2]$ and
$x \in [1/2, 1]$. -/
theorem le_norm_one_sub_mul_exp_two_mul {w : ℂ} (hw : w ∈ UcDisk)
    (him : w.im ∈ Icc (-π / 2) (π / 2)) {x : ℝ} (hx : x ∈ Icc (1 / 2 : ℝ) 1) :
    (1 / 3 : ℝ) * (‖1 - Complex.exp w‖ + (1 - x)) ≤
      ‖1 - (x : ℂ) * Complex.exp (2 * w)‖ := by
  have hw2 : 2 * w ∈ UcDisk := by
    have hre : (2 * w).re = 2 * w.re := by simp [Complex.mul_re]
    rw [mem_UcDisk_iff, hre]
    linarith [mem_UcDisk_iff.mp hw]
  have h1 := le_norm_one_sub_mul_exp hw2 hx
  have h2 := norm_one_sub_exp_le_norm_one_sub_exp_two_mul him
  linarith

/-- High-$x$ bound on `transmuteInnerKernel w x` for $w \in \operatorname{UcDisk}$ with
$\operatorname{Im} w \in [-\pi/2, \pi/2]$ and $x \in [1/2, 1)$:
$$
\|\operatorname{transmuteInnerKernel}(w, x)\| \le
  \sqrt{6} \, (1 - x)^{-1/2} \bigl(\|1 - e^w\| + (1 - x)\bigr)^{-1/2}.
$$ -/
theorem norm_transmuteInnerKernel_le_high {w : ℂ} (hw : w ∈ UcDisk)
    (him : w.im ∈ Icc (-π / 2) (π / 2)) {x : ℝ} (hx : x ∈ Ico (1 / 2 : ℝ) 1) :
    ‖transmuteInnerKernel w x‖ ≤
      Real.sqrt 6 * (1 - x) ^ (-1 / 2 : ℝ) *
        (‖1 - Complex.exp w‖ + (1 - x)) ^ (-1 / 2 : ℝ) := by
  have hx0 : 0 < x := by linarith [hx.1]
  have hx1 : 0 < 1 - x := sub_pos.mpr hx.2
  have hx_ioo : x ∈ Ioo (0 : ℝ) 1 := ⟨hx0, hx.2⟩
  have hx_icc : x ∈ Icc (1 / 2 : ℝ) 1 := ⟨hx.1, hx.2.le⟩
  rw [norm_transmuteInnerKernel_eq hw hx_ioo]
  set u : ℝ := ‖1 - Complex.exp w‖ + (1 - x)
  have hu_pos : 0 < u := add_pos_of_nonneg_of_pos (norm_nonneg _) hx1
  have hx_rpow_le : x ^ (-1 / 2 : ℝ) ≤ Real.sqrt 2 := by
    have h_step : x ^ (-1 / 2 : ℝ) ≤ (1 / 2 : ℝ) ^ (-1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hx.1 (by norm_num)
    have h_sqrt2 : (1 / 2 : ℝ) ^ (-1 / 2 : ℝ) = Real.sqrt 2 := by
      have h1 : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := one_div 2
      have h2 : (-1 / 2 : ℝ) = - (1 / 2 : ℝ) := by ring
      rw [h1, h2, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num),
        inv_inv, ← Real.sqrt_eq_rpow]
    rwa [h_sqrt2] at h_step
  have h2w_ge : (1 / 3 : ℝ) * u ≤ ‖1 - (x : ℂ) * Complex.exp (2 * w)‖ :=
    le_norm_one_sub_mul_exp_two_mul hw him hx_icc
  have h2w_rpow_le :
      ‖1 - (x : ℂ) * Complex.exp (2 * w)‖ ^ (-1 / 2 : ℝ) ≤
        Real.sqrt 3 * u ^ (-1 / 2 : ℝ) := by
    have h_step :
        ‖1 - (x : ℂ) * Complex.exp (2 * w)‖ ^ (-1 / 2 : ℝ) ≤
          ((1 / 3 : ℝ) * u) ^ (-1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) h2w_ge (by norm_num)
    have h_sqrt3 : (1 / 3 : ℝ) ^ (-1 / 2 : ℝ) = Real.sqrt 3 := by
      have h1 : (1 / 3 : ℝ) = (3 : ℝ)⁻¹ := one_div 3
      have h2 : (-1 / 2 : ℝ) = - (1 / 2 : ℝ) := by ring
      rw [h1, h2, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num),
        inv_inv, ← Real.sqrt_eq_rpow]
    rw [Real.mul_rpow (by norm_num) hu_pos.le, h_sqrt3] at h_step
    exact h_step
  have h_sqrt6 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
    rw [← Real.sqrt_mul (by norm_num)]
    norm_num
  calc
    x ^ (-1 / 2 : ℝ) * (1 - x) ^ (-1 / 2 : ℝ) *
        ‖1 - (x : ℂ) * Complex.exp (2 * w)‖ ^ (-1 / 2 : ℝ)
      ≤ Real.sqrt 2 * (1 - x) ^ (-1 / 2 : ℝ) *
          (Real.sqrt 3 * u ^ (-1 / 2 : ℝ)) := by
        refine mul_le_mul
          (mul_le_mul_of_nonneg_right hx_rpow_le (by positivity))
          h2w_rpow_le (by positivity) (by positivity)
    _ = (Real.sqrt 2 * Real.sqrt 3) * (1 - x) ^ (-1 / 2 : ℝ) * u ^ (-1 / 2 : ℝ) := by ring
    _ = Real.sqrt 6 * (1 - x) ^ (-1 / 2 : ℝ) * u ^ (-1 / 2 : ℝ) := by rw [h_sqrt6]

/-- High-$x$ bound on `transmuteInnerDiff f w x` for $w \in \operatorname{UcDisk}$ and
$x \in [1/2, 1)$ (capturing the $(1 - e^w)^2$ second-order cancellation at $e^w = 1$):
$$
\|\operatorname{transmuteInnerDiff}(f, w, x)\| \le
  6 \bigl(\|1 - e^w\| + (1 - x)\bigr) \|f''(w + \log x)\| + 20 \, \|f'(w + \log x)\|.
$$ -/
theorem norm_transmuteInnerDiff_le_high (f : ℂ → ℂ) {w : ℂ} (hw : w ∈ UcDisk)
    {x : ℝ} (hx : x ∈ Ico (1 / 2 : ℝ) 1) :
    ‖transmuteInnerDiff f w x‖ ≤
      6 * (‖1 - Complex.exp w‖ + (1 - x)) *
        ‖deriv (deriv f) (w + (Real.log x : ℂ))‖ +
        20 * ‖deriv f (w + (Real.log x : ℂ))‖ := by
  dsimp [transmuteInnerDiff]
  set z : ℂ := w + (Real.log x : ℂ)
  set u : ℝ := ‖1 - Complex.exp w‖ + (1 - x)
  have hx0 : 0 < x := by linarith [hx.1]
  have hx1 : 0 < 1 - x := sub_pos.mpr hx.2
  have hu_pos : 0 < u := add_pos_of_nonneg_of_pos (norm_nonneg _) hx1
  have hx_icc : x ∈ Icc (1 / 2 : ℝ) 1 := ⟨hx.1, hx.2.le⟩
  have hexp_le1 : ‖Complex.exp w‖ ≤ 1 := by
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    exact (mem_UcDisk_iff.mp hw).le
  have h1_sub_le_u : ‖1 - Complex.exp w‖ ≤ u := by
    dsimp [u]; linarith
  have h1_sub_sq_le : ‖(1 - Complex.exp w) ^ 2‖ ≤ u ^ 2 := by
    rw [norm_pow]
    nlinarith [norm_nonneg (1 - Complex.exp w)]
  have h1_add_sq_le : ‖(1 + Complex.exp w) ^ 2‖ ≤ 4 := by
    have h := norm_add_le (1 : ℂ) (Complex.exp w)
    rw [norm_one] at h
    rw [norm_pow]
    nlinarith [norm_nonneg (1 + Complex.exp w)]
  have hv_le1 : ‖(x : ℂ) * Complex.exp w‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hx0.le]
    nlinarith [hx.2, norm_nonneg (Complex.exp w)]
  have h1_add_v_le2 : ‖1 + (x : ℂ) * Complex.exp w‖ ≤ 2 := by
    have h := norm_add_le (1 : ℂ) ((x : ℂ) * Complex.exp w)
    rw [norm_one] at h
    linarith
  have h1_sub_v_ge : (1 / 3 : ℝ) * u ≤ ‖1 - (x : ℂ) * Complex.exp w‖ :=
    le_norm_one_sub_mul_exp hw hx_icc
  have h1_sub_v_pos : 0 < ‖1 - (x : ℂ) * Complex.exp w‖ :=
    lt_of_lt_of_le (by positivity) h1_sub_v_ge
  have h_coeff2_le :
      ‖(1 - Complex.exp w) ^ 2 *
        ((1 + (x : ℂ) * Complex.exp w) / (1 - (x : ℂ) * Complex.exp w))‖ ≤ 6 * u := by
    rw [norm_mul, norm_div, mul_div_assoc', div_le_iff₀ h1_sub_v_pos]
    have h_num : ‖(1 - Complex.exp w) ^ 2‖ * ‖1 + (x : ℂ) * Complex.exp w‖ ≤ u ^ 2 * 2 :=
      mul_le_mul h1_sub_sq_le h1_add_v_le2 (norm_nonneg _) (sq_nonneg u)
    have h_den : 6 * u * ((1 / 3 : ℝ) * u) ≤ 6 * u * ‖1 - (x : ℂ) * Complex.exp w‖ :=
      mul_le_mul_of_nonneg_left h1_sub_v_ge (by positivity)
    linarith
  have h_coeff1_le :
      ‖(1 - Complex.exp w) ^ 2 *
        ((2 * (x : ℂ) * Complex.exp w) / (1 - (x : ℂ) * Complex.exp w) ^ 2)‖ ≤ 18 := by
    rw [norm_mul, norm_div, norm_pow (1 - (x : ℂ) * Complex.exp w) 2, mul_div_assoc',
      div_le_iff₀ (pow_pos h1_sub_v_pos 2)]
    have h_2v : ‖2 * (x : ℂ) * Complex.exp w‖ ≤ 2 := by
      rw [mul_assoc, norm_mul, Complex.norm_ofNat]
      linarith
    have h_num : ‖(1 - Complex.exp w) ^ 2‖ * ‖2 * (x : ℂ) * Complex.exp w‖ ≤ u ^ 2 * 2 :=
      mul_le_mul h1_sub_sq_le h_2v (norm_nonneg _) (sq_nonneg u)
    have h_sq_ge : ((1 / 3 : ℝ) * u) ^ 2 ≤ ‖1 - (x : ℂ) * Complex.exp w‖ ^ 2 := by
      nlinarith
    linarith
  have h_term_main :
      ‖(1 - Complex.exp w) ^ 2 *
        ((1 + (x : ℂ) * Complex.exp w) / (1 - (x : ℂ) * Complex.exp w) *
          deriv (deriv f) z +
          (2 * (x : ℂ) * Complex.exp w) / (1 - (x : ℂ) * Complex.exp w) ^ 2 *
            deriv f z)‖ ≤
        6 * u * ‖deriv (deriv f) z‖ + 18 * ‖deriv f z‖ := by
    have h_distrib :
        (1 - Complex.exp w) ^ 2 *
          ((1 + (x : ℂ) * Complex.exp w) / (1 - (x : ℂ) * Complex.exp w) *
            deriv (deriv f) z +
            (2 * (x : ℂ) * Complex.exp w) / (1 - (x : ℂ) * Complex.exp w) ^ 2 *
              deriv f z) =
        ((1 - Complex.exp w) ^ 2 *
          ((1 + (x : ℂ) * Complex.exp w) / (1 - (x : ℂ) * Complex.exp w))) *
          deriv (deriv f) z +
        ((1 - Complex.exp w) ^ 2 *
          ((2 * (x : ℂ) * Complex.exp w) / (1 - (x : ℂ) * Complex.exp w) ^ 2)) *
          deriv f z := by ring
    rw [h_distrib]
    calc
      ‖((1 - Complex.exp w) ^ 2 *
          ((1 + (x : ℂ) * Complex.exp w) / (1 - (x : ℂ) * Complex.exp w))) *
          deriv (deriv f) z +
        ((1 - Complex.exp w) ^ 2 *
          ((2 * (x : ℂ) * Complex.exp w) / (1 - (x : ℂ) * Complex.exp w) ^ 2)) *
          deriv f z‖
        ≤ ‖((1 - Complex.exp w) ^ 2 *
            ((1 + (x : ℂ) * Complex.exp w) / (1 - (x : ℂ) * Complex.exp w))) *
            deriv (deriv f) z‖ +
          ‖((1 - Complex.exp w) ^ 2 *
            ((2 * (x : ℂ) * Complex.exp w) / (1 - (x : ℂ) * Complex.exp w) ^ 2)) *
            deriv f z‖ := norm_add_le _ _
      _ = ‖(1 - Complex.exp w) ^ 2 *
            ((1 + (x : ℂ) * Complex.exp w) / (1 - (x : ℂ) * Complex.exp w))‖ *
            ‖deriv (deriv f) z‖ +
          ‖(1 - Complex.exp w) ^ 2 *
            ((2 * (x : ℂ) * Complex.exp w) / (1 - (x : ℂ) * Complex.exp w) ^ 2)‖ *
            ‖deriv f z‖ := by
          rw [norm_mul _ (deriv (deriv f) z), norm_mul _ (deriv f z)]
      _ ≤ 6 * u * ‖deriv (deriv f) z‖ + 18 * ‖deriv f z‖ :=
          add_le_add
            (mul_le_mul_of_nonneg_right h_coeff2_le (norm_nonneg _))
            (mul_le_mul_of_nonneg_right h_coeff1_le (norm_nonneg _))
  have h_term_sub :
      ‖(1 / 2 : ℂ) * (1 + Complex.exp w) ^ 2 * deriv f z‖ ≤ 2 * ‖deriv f z‖ := by
    rw [norm_mul, norm_mul, norm_div, norm_one, Complex.norm_ofNat]
    have : 1 / 2 * ‖(1 + Complex.exp w) ^ 2‖ ≤ 2 := by linarith
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  have h_sub := norm_sub_le
    ((1 - Complex.exp w) ^ 2 *
      ((1 + (x : ℂ) * Complex.exp w) / (1 - (x : ℂ) * Complex.exp w) * deriv (deriv f) z +
        (2 * (x : ℂ) * Complex.exp w) / (1 - (x : ℂ) * Complex.exp w) ^ 2 * deriv f z))
    ((1 / 2 : ℂ) * (1 + Complex.exp w) ^ 2 * deriv f z)
  linarith

/-- **Combined High-$x$ Source-to-Transform Bound**:
If $f : \mathbb{C} \to \mathbb{C}$ satisfies the first- and second-derivative bounds
$\|f'(w + \log x)\| \le C_1 u^{\gamma_{\mathrm{src}} - 1}$ and
$\|f''(w + \log x)\| \le C_2 u^{\gamma_{\mathrm{src}} - 2}$ with
$u = \|1 - e^w\| + (1 - x)$, then for $w \in \operatorname{UcDisk}$ with
$\operatorname{Im} w \in [-\pi/2, \pi/2]$ and $x \in [1/2, 1)$,
$$
\|\operatorname{transmuteInnerKernel}(w, x) \, \operatorname{transmuteInnerDiff}(f, w, x)\|
  \le \sqrt{6} \, (6 C_2 + 20 C_1) \, (1 - x)^{-1/2}
    \bigl(\|1 - e^w\| + (1 - x)\bigr)^{\gamma_{\mathrm{src}} - 3/2}.
$$ -/
theorem norm_transmuteInnerKernel_mul_diff_le_of_source_bound
    {f : ℂ → ℂ} {w : ℂ} (hw : w ∈ UcDisk) (him : w.im ∈ Icc (-π / 2) (π / 2))
    {x : ℝ} (hx : x ∈ Ico (1 / 2 : ℝ) 1)
    {C₁ C₂ γ_src : ℝ} (_hC₁ : 0 ≤ C₁) (_hC₂ : 0 ≤ C₂)
    (hdf₁ : ‖deriv f (w + (Real.log x : ℂ))‖ ≤
      C₁ * (‖1 - Complex.exp w‖ + (1 - x)) ^ (γ_src - 1))
    (hdf₂ : ‖deriv (deriv f) (w + (Real.log x : ℂ))‖ ≤
      C₂ * (‖1 - Complex.exp w‖ + (1 - x)) ^ (γ_src - 2)) :
    ‖transmuteInnerKernel w x * transmuteInnerDiff f w x‖ ≤
      Real.sqrt 6 * (6 * C₂ + 20 * C₁) *
        (1 - x) ^ (-1 / 2 : ℝ) *
        (‖1 - Complex.exp w‖ + (1 - x)) ^ (γ_src - 3 / 2) := by
  set u : ℝ := ‖1 - Complex.exp w‖ + (1 - x)
  have hx1 : 0 < 1 - x := sub_pos.mpr hx.2
  have hu_pos : 0 < u := add_pos_of_nonneg_of_pos (norm_nonneg _) hx1
  have h_ker := norm_transmuteInnerKernel_le_high hw him hx
  have h_diff := norm_transmuteInnerDiff_le_high f hw hx
  have h_u_rpow1 : u * u ^ (γ_src - 2) = u ^ (γ_src - 1) := by
    have : u * u ^ (γ_src - 2) = u ^ (1 : ℝ) * u ^ (γ_src - 2) := by rw [Real.rpow_one]
    rw [this, ← Real.rpow_add hu_pos]
    congr 1; ring
  have h_u_rpow2 : u ^ (-1 / 2 : ℝ) * u ^ (γ_src - 1) = u ^ (γ_src - 3 / 2) := by
    rw [← Real.rpow_add hu_pos]
    congr 1; ring
  have h_diff_bound :
      ‖transmuteInnerDiff f w x‖ ≤ (6 * C₂ + 20 * C₁) * u ^ (γ_src - 1) := by
    calc
      ‖transmuteInnerDiff f w x‖
        ≤ 6 * u * ‖deriv (deriv f) (w + (Real.log x : ℂ))‖ +
            20 * ‖deriv f (w + (Real.log x : ℂ))‖ := h_diff
      _ ≤ 6 * u * (C₂ * u ^ (γ_src - 2)) + 20 * (C₁ * u ^ (γ_src - 1)) := by
          refine add_le_add
            (mul_le_mul_of_nonneg_left hdf₂ (by positivity))
            (mul_le_mul_of_nonneg_left hdf₁ (by positivity))
      _ = 6 * C₂ * (u * u ^ (γ_src - 2)) + 20 * C₁ * u ^ (γ_src - 1) := by ring
      _ = (6 * C₂ + 20 * C₁) * u ^ (γ_src - 1) := by rw [h_u_rpow1]; ring
  rw [norm_mul]
  calc
    ‖transmuteInnerKernel w x‖ * ‖transmuteInnerDiff f w x‖
      ≤ (Real.sqrt 6 * (1 - x) ^ (-1 / 2 : ℝ) * u ^ (-1 / 2 : ℝ)) *
          ((6 * C₂ + 20 * C₁) * u ^ (γ_src - 1)) :=
        mul_le_mul h_ker h_diff_bound (norm_nonneg _) (by positivity)
    _ = Real.sqrt 6 * (6 * C₂ + 20 * C₁) * (1 - x) ^ (-1 / 2 : ℝ) *
          (u ^ (-1 / 2 : ℝ) * u ^ (γ_src - 1)) := by ring
    _ = Real.sqrt 6 * (6 * C₂ + 20 * C₁) * (1 - x) ^ (-1 / 2 : ℝ) *
          u ^ (γ_src - 3 / 2) := by rw [h_u_rpow2]

/-! ## Section 5: Combined Low-$x$ / High-$x$ Integral Bounds and Two-Step Cauchy Estimates -/

/-- Extension of `integral_rpow_neg_half_mul_add_rpow_le` to all $e \in (0, 2]$ (covering
$e = \|1 - e^w\| \in (0, 2]$ for all $w \in \operatorname{UcDisk}$). -/
theorem integral_rpow_neg_half_mul_add_rpow_le_of_le_two {β : ℝ} (hβ : β ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {e : ℝ}, 0 < e → e ≤ 2 →
      (∫ y in (0 : ℝ)..(1 / 2), y ^ (-1 / 2 : ℝ) * (e + y) ^ (-1 / 2 - β)) ≤
        C * (e ^ (-β) + 1) := by
  set α : ℝ := -1 / 2 - β
  set M : ℝ := max 1 ((2 : ℝ) ^ α)
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left 1 ((2 : ℝ) ^ α))
  have hβ_abs_pos : 0 < |β| := abs_pos.mpr hβ
  set C : ℝ := 2 * M + M * ((1 / 2 : ℝ) ^ (-β) + 1) / |β|
  refine ⟨C, by positivity, fun {e} he_pos _he_le => ?_⟩
  set e0 : ℝ := min e (1 / 2)
  have he0_pos : 0 < e0 := lt_min he_pos (by norm_num)
  have he0_le_e : e0 ≤ e := min_le_left e (1 / 2)
  have he0_le_half : e0 ≤ 1 / 2 := min_le_right e (1 / 2)
  have h_int1 : IntervalIntegrable
      (fun y : ℝ => y ^ (-1 / 2 : ℝ) * (e + y) ^ α) volume 0 e0 :=
    intervalIntegrable_rpow_neg_half_mul_add_rpow α le_rfl he0_pos.le he_pos
  have h_int2 : IntervalIntegrable
      (fun y : ℝ => y ^ (-1 / 2 : ℝ) * (e + y) ^ α) volume e0 (1 / 2) :=
    intervalIntegrable_rpow_neg_half_mul_add_rpow α he0_pos.le he0_le_half he_pos
  have h_split := (intervalIntegral.integral_add_adjacent_intervals h_int1 h_int2).symm
  have h_part1 :
      (∫ y in (0 : ℝ)..e0, y ^ (-1 / 2 : ℝ) * (e + y) ^ α) ≤
        2 * M * e ^ (-β) := by
    have h_rhs_int : IntervalIntegrable
        (fun y : ℝ => (M * e ^ α) * y ^ (-1 / 2 : ℝ)) volume 0 e0 :=
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul (M * e ^ α)
    have h_mono :
        (∫ y in (0 : ℝ)..e0, y ^ (-1 / 2 : ℝ) * (e + y) ^ α) ≤
          ∫ y in (0 : ℝ)..e0, (M * e ^ α) * y ^ (-1 / 2 : ℝ) := by
      refine intervalIntegral.integral_mono_on he0_pos.le h_int1 h_rhs_int fun y hy => ?_
      have hy0 : 0 ≤ y := hy.1
      have hye : y ≤ e := hy.2.trans he0_le_e
      have h_add_le : (e + y) ^ α ≤ M * e ^ α :=
        add_rpow_le_max_mul_rpow he_pos (by linarith) (by linarith)
      calc
        y ^ (-1 / 2 : ℝ) * (e + y) ^ α
          ≤ y ^ (-1 / 2 : ℝ) * (M * e ^ α) :=
            mul_le_mul_of_nonneg_left h_add_le (Real.rpow_nonneg hy0 _)
        _ = (M * e ^ α) * y ^ (-1 / 2 : ℝ) := by ring
    rw [intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -1 / 2))] at h_mono
    have h_exp_half : (-1 / 2 : ℝ) + 1 = 1 / 2 := by ring
    rw [h_exp_half, Real.zero_rpow (by norm_num)] at h_mono
    have he0_rpow_le : e0 ^ (1 / 2 : ℝ) ≤ e ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow he0_pos.le he0_le_e (by norm_num)
    have h_eval_le :
        (M * e ^ α) * ((e0 ^ (1 / 2 : ℝ) - 0) / (1 / 2 : ℝ)) ≤
          2 * M * (e ^ α * e ^ (1 / 2 : ℝ)) := by
      calc
        (M * e ^ α) * ((e0 ^ (1 / 2 : ℝ) - 0) / (1 / 2 : ℝ))
          = 2 * M * e ^ α * e0 ^ (1 / 2 : ℝ) := by ring
        _ ≤ 2 * M * e ^ α * e ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left he0_rpow_le (by positivity)
        _ = 2 * M * (e ^ α * e ^ (1 / 2 : ℝ)) := by ring
    have h_rpow_comb : e ^ α * e ^ (1 / 2 : ℝ) = e ^ (-β) := by
      rw [← Real.rpow_add he_pos]
      congr 1; dsimp [α]; ring
    rw [h_rpow_comb] at h_eval_le
    exact h_mono.trans h_eval_le
  have h_part2 :
      (∫ y in e0..(1 / 2), y ^ (-1 / 2 : ℝ) * (e + y) ^ α) ≤
        (M * ((1 / 2 : ℝ) ^ (-β) + 1) / |β|) * (e ^ (-β) + 1) := by
    rcases le_or_gt (1 / 2 : ℝ) e with h_ge | h_lt
    · have he0_eq : e0 = 1 / 2 := min_eq_right h_ge
      rw [he0_eq, intervalIntegral.integral_same]
      positivity
    · have he0_eq : e0 = e := min_eq_left h_lt.le
      rw [he0_eq]
      rw [he0_eq] at h_int2
      have h_rhs_cont : ContinuousOn (fun y : ℝ => M * y ^ (-1 - β)) (uIcc e (1 / 2)) := by
        rw [uIcc_of_le h_lt.le]
        intro y hy
        exact continuousAt_const.continuousWithinAt.mul
          (continuousAt_id.rpow_const (Or.inl (by dsimp; linarith [hy.1]))).continuousWithinAt
      have h_mono :
          (∫ y in e..(1 / 2), y ^ (-1 / 2 : ℝ) * (e + y) ^ α) ≤
            ∫ y in e..(1 / 2), M * y ^ (-1 - β) := by
        refine intervalIntegral.integral_mono_on h_lt.le h_int2
          (h_rhs_cont.intervalIntegrable) fun y hy => ?_
        have hy_pos : 0 < y := lt_of_lt_of_le he_pos hy.1
        have h_add_le : (e + y) ^ α ≤ M * y ^ α :=
          add_rpow_le_max_mul_rpow hy_pos (by linarith) (by linarith [hy.1])
        calc
          y ^ (-1 / 2 : ℝ) * (e + y) ^ α
            ≤ y ^ (-1 / 2 : ℝ) * (M * y ^ α) :=
              mul_le_mul_of_nonneg_left h_add_le (by positivity)
          _ = M * (y ^ (-1 / 2 : ℝ) * y ^ α) := by ring
          _ = M * y ^ (-1 - β) := by
            rw [← Real.rpow_add hy_pos]
            congr 2; dsimp [α]; ring
      have h_ne_neg1 : -1 - β ≠ -1 := by intro h; apply hβ; linarith
      have h_zero_not_mem : (0 : ℝ) ∉ uIcc e (1 / 2) := by
        rw [uIcc_of_le h_lt.le]
        intro h0; linarith [h0.1]
      rw [intervalIntegral.integral_const_mul,
        integral_rpow (Or.inr ⟨h_ne_neg1, h_zero_not_mem⟩)] at h_mono
      have h_exp : -1 - β + 1 = -β := by ring
      rw [h_exp] at h_mono
      have h_quot_le :
          ((1 / 2 : ℝ) ^ (-β) - e ^ (-β)) / (-β) ≤
            ((1 / 2 : ℝ) ^ (-β) + e ^ (-β)) / |β| := by
        calc
          ((1 / 2 : ℝ) ^ (-β) - e ^ (-β)) / (-β)
            ≤ |((1 / 2 : ℝ) ^ (-β) - e ^ (-β)) / (-β)| := le_abs_self _
          _ = |(1 / 2 : ℝ) ^ (-β) - e ^ (-β)| / |β| := by rw [abs_div, abs_neg]
          _ ≤ (|(1 / 2 : ℝ) ^ (-β)| + |e ^ (-β)|) / |β| :=
              div_le_div_of_nonneg_right (abs_sub _ _) hβ_abs_pos.le
          _ = ((1 / 2 : ℝ) ^ (-β) + e ^ (-β)) / |β| := by
              rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
      have h_prod_le :
          (1 / 2 : ℝ) ^ (-β) + e ^ (-β) ≤
            ((1 / 2 : ℝ) ^ (-β) + 1) * (e ^ (-β) + 1) := by
        nlinarith [show (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (-β) by positivity,
          show (0 : ℝ) ≤ e ^ (-β) by positivity]
      calc
        (∫ y in e..(1 / 2), y ^ (-1 / 2 : ℝ) * (e + y) ^ α)
          ≤ M * (((1 / 2 : ℝ) ^ (-β) - e ^ (-β)) / (-β)) := h_mono
        _ ≤ M * (((1 / 2 : ℝ) ^ (-β) + e ^ (-β)) / |β|) :=
            mul_le_mul_of_nonneg_left h_quot_le hM_pos.le
        _ ≤ M * ((((1 / 2 : ℝ) ^ (-β) + 1) * (e ^ (-β) + 1)) / |β|) :=
            mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_right h_prod_le hβ_abs_pos.le) hM_pos.le
        _ = (M * ((1 / 2 : ℝ) ^ (-β) + 1) / |β|) * (e ^ (-β) + 1) := by ring
  rw [h_split]
  calc
    (∫ y in (0 : ℝ)..e0, y ^ (-1 / 2 : ℝ) * (e + y) ^ α) +
        (∫ y in e0..(1 / 2), y ^ (-1 / 2 : ℝ) * (e + y) ^ α)
      ≤ 2 * M * e ^ (-β) +
          (M * ((1 / 2 : ℝ) ^ (-β) + 1) / |β|) * (e ^ (-β) + 1) :=
        add_le_add h_part1 h_part2
    _ ≤ 2 * M * (e ^ (-β) + 1) +
          (M * ((1 / 2 : ℝ) ^ (-β) + 1) / |β|) * (e ^ (-β) + 1) := by
        refine add_le_add ?_ le_rfl
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = C * (e ^ (-β) + 1) := by dsimp [C]; ring

/-- High-$x$ set integral bound on `Ioo (1 / 2 : ℝ) 1` for `transmuteOpInner`:
for any $\gamma_{\mathrm{src}} \ne 1$ and $C_1, C_2 \ge 0$, there exists $C_{\mathrm{high}} \ge 0$
such that whenever $w \in \operatorname{UcDisk}$ with $\operatorname{Im} w \in [-\pi/2, \pi/2]$
and $f$ satisfies the Cauchy derivative bounds on $x \in (1/2, 1)$,
$$
\left\|\int_{x \in (1/2, 1)} \operatorname{transmuteInnerKernel}(w, x) \,
  \operatorname{transmuteInnerDiff}(f, w, x) \, dx\right\|
  \le C_{\mathrm{high}} \Bigl(\|1 - e^w\|^{\gamma_{\mathrm{src}} - 1} + 1\Bigr).
$$ -/
theorem norm_setIntegral_high_transmuteInner_le {γ_src C₁ C₂ : ℝ}
    (hγ : γ_src ≠ 1) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ∃ C_high : ℝ, 0 ≤ C_high ∧ ∀ {w : ℂ}, w ∈ UcDisk →
      w.im ∈ Icc (-π / 2) (π / 2) → ∀ {f : ℂ → ℂ},
      IntegrableOn
        (fun x : ℝ => transmuteInnerKernel w x * transmuteInnerDiff f w x)
        (Ioo (1 / 2 : ℝ) 1) volume →
      (∀ x ∈ Ioo (1 / 2 : ℝ) 1,
        ‖deriv f (w + (Real.log x : ℂ))‖ ≤
          C₁ * (‖1 - Complex.exp w‖ + (1 - x)) ^ (γ_src - 1)) →
      (∀ x ∈ Ioo (1 / 2 : ℝ) 1,
        ‖deriv (deriv f) (w + (Real.log x : ℂ))‖ ≤
          C₂ * (‖1 - Complex.exp w‖ + (1 - x)) ^ (γ_src - 2)) →
      ‖∫ x in Ioo (1 / 2 : ℝ) 1,
        transmuteInnerKernel w x * transmuteInnerDiff f w x‖ ≤
        C_high * (‖1 - Complex.exp w‖ ^ (γ_src - 1) + 1) := by
  have hβ : 1 - γ_src ≠ 0 := sub_ne_zero.mpr hγ.symm
  obtain ⟨C₀, hC₀_nonneg, hC₀⟩ := integral_rpow_neg_half_mul_add_rpow_le_of_le_two hβ
  set K₀ : ℝ := Real.sqrt 6 * (6 * C₂ + 20 * C₁)
  have hK₀_nonneg : 0 ≤ K₀ := by positivity
  refine ⟨K₀ * C₀, mul_nonneg hK₀_nonneg hC₀_nonneg,
    fun {w} hw him {f} h_int hdf₁ hdf₂ => ?_⟩
  set e : ℝ := ‖1 - Complex.exp w‖
  have he_pos : 0 < e :=
    norm_pos_iff.mpr (slitPlane_ne_zero (one_sub_exp_mem_slitPlane hw))
  have he_le2 : e ≤ 2 := by
    have hexp_le1 : ‖Complex.exp w‖ ≤ 1 := by
      rw [Complex.norm_exp, Real.exp_le_one_iff]
      exact (mem_UcDisk_iff.mp hw).le
    have h := norm_sub_le (1 : ℂ) (Complex.exp w)
    rw [norm_one] at h
    dsimp [e]; linarith
  set g : ℝ → ℝ := fun y => y ^ (-1 / 2 : ℝ) * (e + y) ^ (-1 / 2 - (1 - γ_src))
  have hg_int : IntervalIntegrable g volume 0 (1 / 2) :=
    intervalIntegrable_rpow_neg_half_mul_add_rpow (-1 / 2 - (1 - γ_src))
      le_rfl (by norm_num) he_pos
  have hg_comp_int : IntervalIntegrable (fun x : ℝ => g (1 - x)) volume (1 / 2) 1 := by
    have h_sub := hg_int.comp_sub_left 1
    have h1 : (1 : ℝ) - 1 / 2 = 1 / 2 := by ring
    have h2 : (1 : ℝ) - 0 = 1 := by ring
    rw [h1, h2] at h_sub
    exact h_sub.symm
  have hg_integrableOn : IntegrableOn (fun x : ℝ => K₀ * g (1 - x))
      (Ioo (1 / 2 : ℝ) 1) volume :=
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mp hg_comp_int).const_mul K₀
  have h_exp_eq : -1 / 2 - (1 - γ_src) = γ_src - 3 / 2 := by ring
  have h_pt : ∀ x ∈ Ioo (1 / 2 : ℝ) 1,
      ‖transmuteInnerKernel w x * transmuteInnerDiff f w x‖ ≤ K₀ * g (1 - x) := by
    intro x hx
    have h_bd := norm_transmuteInnerKernel_mul_diff_le_of_source_bound hw him
      ⟨hx.1.le, hx.2⟩ hC₁ hC₂ (hdf₁ x hx) (hdf₂ x hx)
    dsimp [K₀, g, e]
    rw [h_exp_eq]
    linarith
  have h_mono :
      ‖∫ x in Ioo (1 / 2 : ℝ) 1,
        transmuteInnerKernel w x * transmuteInnerDiff f w x‖ ≤
        K₀ * ∫ x in Ioo (1 / 2 : ℝ) 1, g (1 - x) := by
    calc
      ‖∫ x in Ioo (1 / 2 : ℝ) 1,
        transmuteInnerKernel w x * transmuteInnerDiff f w x‖
        ≤ ∫ x in Ioo (1 / 2 : ℝ) 1,
            ‖transmuteInnerKernel w x * transmuteInnerDiff f w x‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ x in Ioo (1 / 2 : ℝ) 1, K₀ * g (1 - x) :=
          setIntegral_mono_on h_int.norm hg_integrableOn measurableSet_Ioo h_pt
      _ = K₀ * ∫ x in Ioo (1 / 2 : ℝ) 1, g (1 - x) :=
          integral_const_mul K₀ _
  have h_cov :
      (∫ x in Ioo (1 / 2 : ℝ) 1, g (1 - x)) = ∫ y in (0 : ℝ)..(1 / 2), g y := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    have h_comp := intervalIntegral.integral_comp_sub_left g (1 : ℝ) (a := 1 / 2) (b := 1)
    have h1 : (1 : ℝ) - 1 = 0 := by ring
    have h2 : (1 : ℝ) - 1 / 2 = 1 / 2 := by ring
    rw [h1, h2] at h_comp
    exact h_comp
  have h_neg_beta : -(1 - γ_src) = γ_src - 1 := by ring
  have h_tail := hC₀ he_pos he_le2
  rw [h_neg_beta] at h_tail
  calc
    ‖∫ x in Ioo (1 / 2 : ℝ) 1,
      transmuteInnerKernel w x * transmuteInnerDiff f w x‖
      ≤ K₀ * ∫ x in Ioo (1 / 2 : ℝ) 1, g (1 - x) := h_mono
    _ = K₀ * ∫ y in (0 : ℝ)..(1 / 2), g y := by rw [h_cov]
    _ ≤ K₀ * (C₀ * (e ^ (γ_src - 1) + 1)) :=
        mul_le_mul_of_nonneg_left h_tail hK₀_nonneg
    _ = (K₀ * C₀) * (e ^ (γ_src - 1) + 1) := by ring

/-- Low-$x$ set integral bound on `Ioc (0 : ℝ) (1 / 2)` for `transmuteOpInner`:
if $\|f'(w + \log x)\| \le M_1$ and $\|f''(w + \log x)\| \le M_2$ for all $x \in (0, 1/2]$, then
$$
\left\|\int_{x \in (0, 1/2]} \operatorname{transmuteInnerKernel}(w, x) \,
  \operatorname{transmuteInnerDiff}(f, w, x) \, dx\right\|
  \le 2 \sqrt{2} \, (16 M_2 + 18 M_1).
$$ -/
theorem norm_setIntegral_low_transmuteInner_le {w : ℂ} (hw : w ∈ UcDisk)
    {f : ℂ → ℂ} {M₁ M₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (h_int : IntegrableOn
      (fun x : ℝ => transmuteInnerKernel w x * transmuteInnerDiff f w x)
      (Ioc (0 : ℝ) (1 / 2)) volume)
    (hdf₁ : ∀ x ∈ Ioc (0 : ℝ) (1 / 2),
      ‖deriv f (w + (Real.log x : ℂ))‖ ≤ M₁)
    (hdf₂ : ∀ x ∈ Ioc (0 : ℝ) (1 / 2),
      ‖deriv (deriv f) (w + (Real.log x : ℂ))‖ ≤ M₂) :
    ‖∫ x in Ioc (0 : ℝ) (1 / 2),
      transmuteInnerKernel w x * transmuteInnerDiff f w x‖ ≤
      2 * Real.sqrt 2 * (16 * M₂ + 18 * M₁) := by
  set D : ℝ := 16 * M₂ + 18 * M₁
  have hD_nonneg : 0 ≤ D := by positivity
  have h_pt : ∀ x ∈ Ioc (0 : ℝ) (1 / 2),
      ‖transmuteInnerKernel w x * transmuteInnerDiff f w x‖ ≤
        (2 * D) * x ^ (-1 / 2 : ℝ) := by
    intro x hx
    have hx0 : 0 < x := hx.1
    have h1x_ge : 1 / 2 ≤ 1 - x := by linarith [hx.2]
    have h1x_rpow_le : (1 - x) ^ (-1 / 2 : ℝ) ≤ Real.sqrt 2 := by
      have h_step : (1 - x) ^ (-1 / 2 : ℝ) ≤ (1 / 2 : ℝ) ^ (-1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) h1x_ge (by norm_num)
      have h_sqrt2 : (1 / 2 : ℝ) ^ (-1 / 2 : ℝ) = Real.sqrt 2 := by
        have h1 : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := one_div 2
        have h2 : (-1 / 2 : ℝ) = - (1 / 2 : ℝ) := by ring
        rw [h1, h2, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num),
          inv_inv, ← Real.sqrt_eq_rpow]
      rwa [h_sqrt2] at h_step
    have h_ker_le : ‖transmuteInnerKernel w x‖ ≤ 2 * x ^ (-1 / 2 : ℝ) := by
      calc
        ‖transmuteInnerKernel w x‖
          ≤ Real.sqrt 2 * x ^ (-1 / 2 : ℝ) * (1 - x) ^ (-1 / 2 : ℝ) :=
            norm_transmuteInnerKernel_le hw hx
        _ ≤ Real.sqrt 2 * x ^ (-1 / 2 : ℝ) * Real.sqrt 2 :=
            mul_le_mul_of_nonneg_left h1x_rpow_le (by positivity)
        _ = (Real.sqrt 2 * Real.sqrt 2) * x ^ (-1 / 2 : ℝ) := by ring
        _ = 2 * x ^ (-1 / 2 : ℝ) := by rw [Real.mul_self_sqrt (by norm_num)]
    have h_diff_le : ‖transmuteInnerDiff f w x‖ ≤ D := by
      calc
        ‖transmuteInnerDiff f w x‖
          ≤ 16 * ‖deriv (deriv f) (w + (Real.log x : ℂ))‖ +
              18 * ‖deriv f (w + (Real.log x : ℂ))‖ :=
            norm_transmuteInnerDiff_le f hw hx
        _ ≤ 16 * M₂ + 18 * M₁ :=
            add_le_add
              (mul_le_mul_of_nonneg_left (hdf₂ x hx) (by norm_num))
              (mul_le_mul_of_nonneg_left (hdf₁ x hx) (by norm_num))
        _ = D := rfl
    rw [norm_mul]
    calc
      ‖transmuteInnerKernel w x‖ * ‖transmuteInnerDiff f w x‖
        ≤ (2 * x ^ (-1 / 2 : ℝ)) * D :=
          mul_le_mul h_ker_le h_diff_le (norm_nonneg _) (by positivity)
      _ = (2 * D) * x ^ (-1 / 2 : ℝ) := by ring
  have h_rpow_int : IntervalIntegrable (fun x : ℝ => x ^ (-1 / 2 : ℝ)) volume 0 (1 / 2) :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have h_rhs_int : IntegrableOn (fun x : ℝ => (2 * D) * x ^ (-1 / 2 : ℝ))
      (Ioc (0 : ℝ) (1 / 2)) volume :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp h_rpow_int).const_mul (2 * D)
  have h_eval_rpow : (∫ x in Ioc (0 : ℝ) (1 / 2), x ^ (-1 / 2 : ℝ)) = Real.sqrt 2 := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2),
      integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -1 / 2))]
    have h_exp : (-1 / 2 : ℝ) + 1 = 1 / 2 := by ring
    have h_half_rpow : (1 / 2 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 2 / 2 := by
      rw [← Real.sqrt_eq_rpow, one_div, Real.sqrt_inv]
      have h2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
      apply mul_right_cancel₀ h2
      rw [inv_mul_cancel₀ h2, div_mul_eq_mul_div, Real.mul_self_sqrt (by norm_num),
        div_self (by norm_num)]
    rw [h_exp, Real.zero_rpow (by norm_num), h_half_rpow]
    ring
  calc
    ‖∫ x in Ioc (0 : ℝ) (1 / 2),
      transmuteInnerKernel w x * transmuteInnerDiff f w x‖
      ≤ ∫ x in Ioc (0 : ℝ) (1 / 2),
          ‖transmuteInnerKernel w x * transmuteInnerDiff f w x‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x in Ioc (0 : ℝ) (1 / 2), (2 * D) * x ^ (-1 / 2 : ℝ) :=
        setIntegral_mono_on h_int.norm h_rhs_int measurableSet_Ioc h_pt
    _ = (2 * D) * ∫ x in Ioc (0 : ℝ) (1 / 2), x ^ (-1 / 2 : ℝ) :=
        integral_const_mul (2 * D) _
    _ = 2 * Real.sqrt 2 * D := by rw [h_eval_rpow]; ring

/-- **First-Order Cauchy Derivative Estimate on a Closed Ball**:
If $g : \mathbb{C} \to \mathbb{C}$ is holomorphic on an open set $U \subseteq \mathbb{C}$,
$\overline{B}(z_0, r) \subseteq U$ with $r > 0$, and $\|g(z)\| \le M$ on $\overline{B}(z_0, r)$,
then $\|g'(z_0)\| \le M / r$. -/
theorem norm_deriv_le_of_ball_bound {U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) {z₀ : ℂ} {r M : ℝ} (hr : 0 < r)
    (h_sub : Metric.closedBall z₀ r ⊆ U)
    (hM : ∀ z ∈ Metric.closedBall z₀ r, ‖g z‖ ≤ M) :
    ‖deriv g z₀‖ ≤ M / r := by
  rw [← Complex.cderiv_eq_deriv hU hg hr h_sub]
  exact Complex.norm_cderiv_le hr (fun z hz => hM z (Metric.sphere_subset_closedBall hz))

/-- **Second-Order Cauchy Derivative Estimate on a Closed Ball**:
If $g : \mathbb{C} \to \mathbb{C}$ is holomorphic on an open set $U \subseteq \mathbb{C}$,
$\overline{B}(z_0, r) \subseteq U$ with $r > 0$, and $\|g(z)\| \le M$ on $\overline{B}(z_0, r)$,
then $\|g''(z_0)\| \le 4 M / r^2$. -/
theorem norm_deriv2_le_of_ball_bound {U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) {z₀ : ℂ} {r M : ℝ} (hr : 0 < r)
    (h_sub : Metric.closedBall z₀ r ⊆ U)
    (hM : ∀ z ∈ Metric.closedBall z₀ r, ‖g z‖ ≤ M) :
    ‖deriv (deriv g) z₀‖ ≤ 4 * M / r ^ 2 := by
  have hr2 : 0 < r / 2 := half_pos hr
  have hg' : DifferentiableOn ℂ (deriv g) U := hg.deriv hU
  have h_sub2 : Metric.closedBall z₀ (r / 2) ⊆ U :=
    (Metric.closedBall_subset_closedBall (half_le_self hr.le)).trans h_sub
  have h_step := norm_deriv_le_of_ball_bound hU hg' hr2 h_sub2 (M := M / (r / 2)) fun w hw => by
    have hw_sub : Metric.closedBall w (r / 2) ⊆ Metric.closedBall z₀ r := by
      intro z hz
      rw [Metric.mem_closedBall] at hw hz ⊢
      calc
        dist z z₀ ≤ dist z w + dist w z₀ := dist_triangle z w z₀
        _ ≤ r / 2 + r / 2 := add_le_add hz hw
        _ = r := add_halves r
    exact norm_deriv_le_of_ball_bound hU hg hr2 (hw_sub.trans h_sub)
      (fun z hz => hM z (hw_sub hz))
  have h_eq : (M / (r / 2)) / (r / 2) = 4 * M / r ^ 2 := by
    have hr_ne : r ≠ 0 := hr.ne'
    field_simp [hr_ne]
    ring
  rwa [h_eq] at h_step

/-- **Combined Low-$x$ / High-$x$ Bound on `transmuteOpInner f w`**:
For any $\gamma_{\mathrm{src}} \ne 1$ and $M_1, M_2, C_1, C_2 \ge 0$, there exists $C \ge 0$
such that for all $w \in \operatorname{UcDisk}$ with $\operatorname{Im} w \in [-\pi/2, \pi/2]$ and
any $f : \mathbb{C} \to \mathbb{C}$ satisfying the low-$x$ bounds on $(0, 1/2]$ and the high-$x$
bounds on $(1/2, 1)$,
$$
\|\operatorname{transmuteOpInner}(f)(w)\|
  \le C \Bigl(\|1 - e^w\|^{\gamma_{\mathrm{src}} - 1} + 1\Bigr).
$$ -/
theorem norm_transmuteOpInner_le_of_split_bounds {γ_src M₁ M₂ C₁ C₂ : ℝ}
    (hγ : γ_src ≠ 1) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {w : ℂ}, w ∈ UcDisk →
      w.im ∈ Icc (-π / 2) (π / 2) → ∀ {f : ℂ → ℂ},
      IntegrableOn
        (fun x : ℝ => transmuteInnerKernel w x * transmuteInnerDiff f w x)
        (Ioo (0 : ℝ) 1) volume →
      (∀ x ∈ Ioc (0 : ℝ) (1 / 2),
        ‖deriv f (w + (Real.log x : ℂ))‖ ≤ M₁) →
      (∀ x ∈ Ioc (0 : ℝ) (1 / 2),
        ‖deriv (deriv f) (w + (Real.log x : ℂ))‖ ≤ M₂) →
      (∀ x ∈ Ioo (1 / 2 : ℝ) 1,
        ‖deriv f (w + (Real.log x : ℂ))‖ ≤
          C₁ * (‖1 - Complex.exp w‖ + (1 - x)) ^ (γ_src - 1)) →
      (∀ x ∈ Ioo (1 / 2 : ℝ) 1,
        ‖deriv (deriv f) (w + (Real.log x : ℂ))‖ ≤
          C₂ * (‖1 - Complex.exp w‖ + (1 - x)) ^ (γ_src - 2)) →
      ‖transmuteOpInner f w‖ ≤ C * (‖1 - Complex.exp w‖ ^ (γ_src - 1) + 1) := by
  obtain ⟨C_high, hC_high_nonneg, hC_high⟩ :=
    norm_setIntegral_high_transmuteInner_le hγ hC₁ hC₂
  set C_low : ℝ := 2 * Real.sqrt 2 * (16 * M₂ + 18 * M₁)
  have hC_low_nonneg : 0 ≤ C_low := by positivity
  refine ⟨(Real.sqrt π)⁻¹ * (C_low + C_high), by positivity,
    fun {w} hw him {f} h_int hlow₁ hlow₂ hhigh₁ hhigh₂ => ?_⟩
  have h_union : Ioc (0 : ℝ) (1 / 2) ∪ Ioo (1 / 2 : ℝ) 1 = Ioo (0 : ℝ) 1 :=
    Ioc_union_Ioo_eq_Ioo (by norm_num) (by norm_num)
  have h_int_low : IntegrableOn
      (fun x : ℝ => transmuteInnerKernel w x * transmuteInnerDiff f w x)
      (Ioc (0 : ℝ) (1 / 2)) volume :=
    h_int.mono_set (by rw [← h_union]; exact subset_union_left)
  have h_int_high : IntegrableOn
      (fun x : ℝ => transmuteInnerKernel w x * transmuteInnerDiff f w x)
      (Ioo (1 / 2 : ℝ) 1) volume :=
    h_int.mono_set (by rw [← h_union]; exact subset_union_right)
  have h_split :
      (∫ x in Ioo (0 : ℝ) 1, transmuteInnerKernel w x * transmuteInnerDiff f w x) =
        (∫ x in Ioc (0 : ℝ) (1 / 2), transmuteInnerKernel w x * transmuteInnerDiff f w x) +
          (∫ x in Ioo (1 / 2 : ℝ) 1, transmuteInnerKernel w x * transmuteInnerDiff f w x) := by
    rw [← h_union]
    exact setIntegral_union
      (Set.disjoint_left.mpr fun x hx1 hx2 => by linarith [hx1.2, hx2.1])
      measurableSet_Ioo h_int_low h_int_high
  have h_low_bd := norm_setIntegral_low_transmuteInner_le hw hM₁ hM₂ h_int_low hlow₁ hlow₂
  have h_high_bd := hC_high hw him h_int_high hhigh₁ hhigh₂
  have he_rpow_nonneg : 0 ≤ ‖1 - Complex.exp w‖ ^ (γ_src - 1) := by positivity
  dsimp [transmuteOpInner]
  rw [h_split, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg π)]
  calc
    (Real.sqrt π)⁻¹ *
        ‖(∫ x in Ioc (0 : ℝ) (1 / 2), transmuteInnerKernel w x * transmuteInnerDiff f w x) +
          (∫ x in Ioo (1 / 2 : ℝ) 1, transmuteInnerKernel w x * transmuteInnerDiff f w x)‖
      ≤ (Real.sqrt π)⁻¹ *
          (‖∫ x in Ioc (0 : ℝ) (1 / 2), transmuteInnerKernel w x * transmuteInnerDiff f w x‖ +
            ‖∫ x in Ioo (1 / 2 : ℝ) 1, transmuteInnerKernel w x * transmuteInnerDiff f w x‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ ≤ (Real.sqrt π)⁻¹ *
          (C_low + C_high * (‖1 - Complex.exp w‖ ^ (γ_src - 1) + 1)) :=
        mul_le_mul_of_nonneg_left (add_le_add h_low_bd h_high_bd) (by positivity)
    _ ≤ (Real.sqrt π)⁻¹ *
          (C_low * (‖1 - Complex.exp w‖ ^ (γ_src - 1) + 1) +
            C_high * (‖1 - Complex.exp w‖ ^ (γ_src - 1) + 1)) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ le_rfl) (by positivity)
        nlinarith
    _ = ((Real.sqrt π)⁻¹ * (C_low + C_high)) *
          (‖1 - Complex.exp w‖ ^ (γ_src - 1) + 1) := by ring

/-! ## Section 6: Folded $\theta$-Contour Integral Bound for `transmuteOpInner` -/

/-- **Folded $\theta$-Contour Integral Bound for `transmuteOpInner`**:
Given $\Delta_\phi > 0$, $h_{\mathrm{gap}} > 0$ with $2(h_{\mathrm{gap}} - \Delta_\phi) \ne 1$
and $2(h_{\mathrm{gap}} - \Delta_\phi) - 1 \ne -1$, and constants $M_1, M_2, C_1, C_2 \ge 0$,
there exists $C_{\mathrm{fold}} \ge 0$ such that for all $k \ge 1$ and any family
$R : \mathbb{R} \to \mathbb{C} \to \mathbb{C}$ satisfying the low-$x$ ($M_1, M_2$) and high-$x$
($C_1, C_2$ with $\gamma_{\mathrm{src}} = 2(h_{\mathrm{gap}} - \Delta_\phi)$) bounds along the
folded contour $w_r(\theta) = -1/(2k) + i\theta$ ($\theta \in [-\pi/2, \pi/2]$),
$$
\left\|(2k)^{-2\Delta_\phi} \frac{1}{\pi} \int_{-\pi/2}^{\pi/2}
  e^{-2k(-1/(2k) + i\theta)} \,
  \operatorname{transmuteOpInner}(R_\theta)\!\left(-\frac{1}{2k} + i\theta\right) d\theta\right\|
  \le C_{\mathrm{fold}} \Bigl((2k)^{-2 h_{\mathrm{gap}}} + (2k)^{-2\Delta_\phi}\Bigr).
$$ -/
theorem norm_folded_integral_transmuteOpInner_le {Δ_phi h_gap M₁ M₂ C₁ C₂ : ℝ}
    (_hΔ : 0 < Δ_phi) (_hh : 0 < h_gap)
    (hγ_ne1 : 2 * (h_gap - Δ_phi) ≠ 1)
    (hα_ne : 2 * (h_gap - Δ_phi) - 1 ≠ -1)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ∃ C_fold : ℝ, 0 ≤ C_fold ∧ ∀ {k : ℕ}, 1 ≤ k → ∀ {R : ℝ → ℂ → ℂ},
      (∀ θ ∈ Icc (-π / 2) (π / 2),
        IntegrableOn
          (fun x : ℝ =>
            transmuteInnerKernel (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ) + (θ : ℂ) * I) x *
              transmuteInnerDiff (R θ) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ) + (θ : ℂ) * I) x)
          (Ioo (0 : ℝ) 1) volume) →
      (∀ θ ∈ Icc (-π / 2) (π / 2), ∀ x ∈ Ioc (0 : ℝ) (1 / 2),
        ‖deriv (R θ) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ) + (θ : ℂ) * I + (Real.log x : ℂ))‖ ≤ M₁) →
      (∀ θ ∈ Icc (-π / 2) (π / 2), ∀ x ∈ Ioc (0 : ℝ) (1 / 2),
        ‖deriv (deriv (R θ))
          (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ) + (θ : ℂ) * I + (Real.log x : ℂ))‖ ≤ M₂) →
      (∀ θ ∈ Icc (-π / 2) (π / 2), ∀ x ∈ Ioo (1 / 2 : ℝ) 1,
        ‖deriv (R θ) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ) + (θ : ℂ) * I + (Real.log x : ℂ))‖ ≤
          C₁ *
            (‖1 - Complex.exp (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ) + (θ : ℂ) * I)‖ + (1 - x)) ^
              (2 * (h_gap - Δ_phi) - 1)) →
      (∀ θ ∈ Icc (-π / 2) (π / 2), ∀ x ∈ Ioo (1 / 2 : ℝ) 1,
        ‖deriv (deriv (R θ))
          (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ) + (θ : ℂ) * I + (Real.log x : ℂ))‖ ≤
          C₂ *
            (‖1 - Complex.exp (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ) + (θ : ℂ) * I)‖ + (1 - x)) ^
              (2 * (h_gap - Δ_phi) - 2)) →
      ‖(((2 * (k : ℝ)) ^ (- (2 * Δ_phi)) : ℝ) : ℂ) *
          ((π : ℂ)⁻¹ * ∫ θ in (-π / 2)..(π / 2),
            Complex.exp (- ((2 * (k : ℤ) : ℤ) : ℂ) *
              (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ) + (θ : ℂ) * I)) *
              transmuteOpInner (R θ) (((-1 / (2 * (k : ℝ)) : ℝ) : ℂ) + (θ : ℂ) * I))‖ ≤
        C_fold * ((2 * (k : ℝ)) ^ (- (2 * h_gap)) + (2 * (k : ℝ)) ^ (- (2 * Δ_phi))) := by
  obtain ⟨C_pt, hC_pt_nonneg, hC_pt⟩ :=
    norm_transmuteOpInner_le_of_split_bounds hγ_ne1 hM₁ hM₂ hC₁ hC₂
  obtain ⟨C_int, hC_int_nonneg, hC_int⟩ :=
    integral_norm_one_sub_exp_rpow_le hα_ne
  set C_fold : ℝ := π⁻¹ * (Real.exp 1 * C_pt) * (C_int + π)
  refine ⟨C_fold, by positivity, fun {k} hk1 {R} h_int hlow₁ hlow₂ hhigh₁ hhigh₂ => ?_⟩
  have h2k_pos : (0 : ℝ) < 2 * (k : ℝ) := by exact_mod_cast (by omega : 0 < 2 * k)
  set ε : ℝ := 1 / (2 * (k : ℝ))
  have hε_pos : 0 < ε := by positivity
  have hε_le : ε ≤ 1 / 2 := by
    dsimp [ε]
    have : (2 : ℝ) ≤ 2 * (k : ℝ) := by
      have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      linarith
    exact one_div_le_one_div_of_le (by norm_num) this
  set wr0 : ℂ := ((-1 / (2 * (k : ℝ)) : ℝ) : ℂ)
  have hwr0_eq : wr0 = (-ε : ℂ) := by dsimp [wr0, ε]; push_cast; ring
  have h_cont_rpow :
      Continuous (fun θ : ℝ =>
        ‖1 - Complex.exp ((-ε : ℂ) + (θ : ℂ) * I)‖ ^ (2 * (h_gap - Δ_phi) - 1)) := by
    refine Continuous.rpow_const (by fun_prop) (fun θ => Or.inl ?_)
    have hw : (-ε : ℂ) + (θ : ℂ) * I ∈ UcDisk := by
      rw [mem_UcDisk_iff]; simp [hε_pos]
    exact norm_ne_zero_iff.mpr (slitPlane_ne_zero (one_sub_exp_mem_slitPlane hw))
  have h_cont_bound :
      Continuous (fun θ : ℝ =>
        (Real.exp 1 * C_pt) *
          (‖1 - Complex.exp ((-ε : ℂ) + (θ : ℂ) * I)‖ ^ (2 * (h_gap - Δ_phi) - 1) + 1)) :=
    continuous_const.mul (h_cont_rpow.add continuous_const)
  have h_int_bound :
      ‖∫ θ in (-π / 2)..(π / 2),
          Complex.exp (- ((2 * (k : ℤ) : ℤ) : ℂ) * (wr0 + (θ : ℂ) * I)) *
            transmuteOpInner (R θ) (wr0 + (θ : ℂ) * I)‖ ≤
        ∫ θ in (-π / 2)..(π / 2),
          (Real.exp 1 * C_pt) *
            (‖1 - Complex.exp ((-ε : ℂ) + (θ : ℂ) * I)‖ ^ (2 * (h_gap - Δ_phi) - 1) + 1) := by
    refine intervalIntegral.norm_integral_le_of_norm_le (by linarith [Real.pi_pos])
      (Eventually.of_forall (fun θ hθ => ?_)) (h_cont_bound.intervalIntegrable _ _)
    have hθ_Icc : θ ∈ Icc (-π / 2) (π / 2) := ⟨hθ.1.le, hθ.2⟩
    set wr : ℂ := wr0 + (θ : ℂ) * I
    have hwr_eq : wr = (-ε : ℂ) + (θ : ℂ) * I := by dsimp [wr]; rw [hwr0_eq]
    have hwr : wr ∈ UcDisk := by
      rw [hwr_eq, mem_UcDisk_iff]; simp [hε_pos]
    have hwr_im : wr.im ∈ Icc (-π / 2) (π / 2) := by
      rw [hwr_eq]; simpa using hθ_Icc
    have h_exp_norm : ‖Complex.exp (- ((2 * (k : ℤ) : ℤ) : ℂ) * wr)‖ = Real.exp 1 := by
      rw [hwr_eq, Complex.norm_exp]
      congr 1
      dsimp [ε]
      have hre : (- ((2 * (k : ℤ) : ℤ) : ℂ) *
          ((-((1 / (2 * (k : ℝ)) : ℝ) : ℂ)) + (θ : ℂ) * I)).re =
          (2 * (k : ℝ)) * (1 / (2 * (k : ℝ))) := by
        simp [Complex.mul_re]
      rw [hre, mul_one_div_cancel h2k_pos.ne']
    have h_pt := hC_pt hwr hwr_im (h_int θ hθ_Icc) (hlow₁ θ hθ_Icc) (hlow₂ θ hθ_Icc)
      (hhigh₁ θ hθ_Icc) (hhigh₂ θ hθ_Icc)
    rw [norm_mul, h_exp_norm, ← hwr_eq, mul_assoc]
    exact mul_le_mul_of_nonneg_left h_pt (Real.exp_pos 1).le
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (h_cont_rpow.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul, mul_one] at h_int_bound
  have h_len : π / 2 - -π / 2 = π := by ring
  rw [h_len] at h_int_bound
  have h_sum_int :
      (∫ θ in (-π / 2)..(π / 2),
        ‖1 - Complex.exp ((-ε : ℂ) + (θ : ℂ) * I)‖ ^ (2 * (h_gap - Δ_phi) - 1)) + π ≤
        (C_int + π) * (ε ^ (2 * (h_gap - Δ_phi) - 1 + 1) + 1) := by
    have h1 := hC_int hε_pos hε_le
    have h2 : 0 ≤ ε ^ (2 * (h_gap - Δ_phi) - 1 + 1) := by positivity
    nlinarith [Real.pi_pos]
  have h_rpow_alg :
      (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) * (ε ^ (2 * (h_gap - Δ_phi) - 1 + 1) + 1) =
        (2 * (k : ℝ)) ^ (- (2 * h_gap)) + (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) := by
    rw [mul_add, mul_one]
    congr 1
    dsimp [ε]
    rw [one_div, Real.inv_rpow h2k_pos.le, ← Real.rpow_neg h2k_pos.le,
      ← Real.rpow_add h2k_pos]
    ring_nf
  rw [norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (rpow_nonneg h2k_pos.le _),
    norm_inv, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  calc
    (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
        (π⁻¹ * ‖∫ θ in (-π / 2)..(π / 2),
          Complex.exp (- ((2 * (k : ℤ) : ℤ) : ℂ) * (wr0 + (θ : ℂ) * I)) *
            transmuteOpInner (R θ) (wr0 + (θ : ℂ) * I)‖)
      ≤ (2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
          (π⁻¹ * ((Real.exp 1 * C_pt) *
            ((C_int + π) * (ε ^ (2 * (h_gap - Δ_phi) - 1 + 1) + 1)))) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (h_int_bound.trans (mul_le_mul_of_nonneg_left h_sum_int (by positivity)))
            (by positivity))
          (by positivity)
    _ = C_fold *
          ((2 * (k : ℝ)) ^ (- (2 * Δ_phi)) *
            (ε ^ (2 * (h_gap - Δ_phi) - 1 + 1) + 1)) := by
        dsimp [C_fold]; ring
    _ = C_fold * ((2 * (k : ℝ)) ^ (- (2 * h_gap)) + (2 * (k : ℝ)) ^ (- (2 * Δ_phi))) := by
        rw [h_rpow_alg]

/-! ## Section 7: Low-$x$ and High-$x$ Cauchy Reduction Lemmas -/

/-- For $x \in (0, 1/2]$, $\log x < -1/2$. -/
lemma log_lt_neg_half_of_mem_Ioc {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) (1 / 2)) :
    Real.log x < -1 / 2 := by
  have h_le : Real.log x ≤ Real.log (1 / 2) := Real.log_le_log hx.1 hx.2
  have h_exp : (1 / 2 : ℝ) < Real.exp (-1 / 2) := by
    have h := Real.add_one_lt_exp (by norm_num : (-1 / 2 : ℝ) ≠ 0)
    linarith
  have h_lt : Real.log (1 / 2) < -1 / 2 := by
    have h := Real.log_lt_log (by norm_num) h_exp
    rwa [Real.log_exp] at h
  exact lt_of_le_of_lt h_le h_lt

/-- For $w \in \operatorname{UcDisk}$ and $x \in (0, 1/2]$, every point
$z \in \overline{B}(w + \log x, 1/4)$ satisfies $\operatorname{Re} z \le -1/4$ (and in particular
$z \in \operatorname{UcDisk}$). -/
lemma re_le_neg_quarter_of_mem_closedBall_add_log {w : ℂ} (hw : w ∈ UcDisk)
    {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) (1 / 2))
    {z : ℂ} (hz : z ∈ Metric.closedBall (w + (Real.log x : ℂ)) (1 / 4)) :
    z.re ≤ -1 / 4 := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have h_re_diff : (z - (w + (Real.log x : ℂ))).re ≤ 1 / 4 :=
    (Complex.re_le_norm _).trans hz
  have h_re_center : (w + (Real.log x : ℂ)).re < -1 / 2 := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith [mem_UcDisk_iff.mp hw, log_lt_neg_half_of_mem_Ioc hx]
  have h_sub_re : (z - (w + (Real.log x : ℂ))).re = z.re - (w + (Real.log x : ℂ)).re :=
    Complex.sub_re _ _
  linarith

lemma closedBall_add_log_subset_UcDisk {w : ℂ} (hw : w ∈ UcDisk)
    {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) (1 / 2)) :
    Metric.closedBall (w + (Real.log x : ℂ)) (1 / 4) ⊆ UcDisk := by
  intro z hz
  rw [mem_UcDisk_iff]
  linarith [re_le_neg_quarter_of_mem_closedBall_add_log hw hx hz]

/-- **Low-$x$ Cauchy Derivative Bounds from Half-Plane Boundedness**:
If $f : \mathbb{C} \to \mathbb{C}$ is holomorphic on $\operatorname{UcDisk}$ and satisfies
$\|f(z)\| \le M_0$ for all $z$ with $\operatorname{Re} z \le -1/4$, then for all
$w \in \operatorname{UcDisk}$ and $x \in (0, 1/2]$,
$$\|f'(w + \log x)\| \le 4 M_0 \qquad \text{and} \qquad \|f''(w + \log x)\| \le 64 M_0.$$ -/
theorem norm_deriv_and_deriv2_add_log_le_of_re_le {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f UcDisk) {M₀ : ℝ}
    (hM₀ : ∀ z : ℂ, z.re ≤ -1 / 4 → ‖f z‖ ≤ M₀)
    {w : ℂ} (hw : w ∈ UcDisk) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) (1 / 2)) :
    ‖deriv f (w + (Real.log x : ℂ))‖ ≤ 4 * M₀ ∧
      ‖deriv (deriv f) (w + (Real.log x : ℂ))‖ ≤ 64 * M₀ := by
  have h_sub := closedBall_add_log_subset_UcDisk hw hx
  have h_ball : ∀ z ∈ Metric.closedBall (w + (Real.log x : ℂ)) (1 / 4), ‖f z‖ ≤ M₀ :=
    fun z hz => hM₀ z (re_le_neg_quarter_of_mem_closedBall_add_log hw hx hz)
  have hd1 := norm_deriv_le_of_ball_bound isOpen_UcDisk hf (by norm_num : (0 : ℝ) < 1 / 4)
    h_sub h_ball
  have hd2 := norm_deriv2_le_of_ball_bound isOpen_UcDisk hf (by norm_num : (0 : ℝ) < 1 / 4)
    h_sub h_ball
  have h1 : M₀ / (1 / 4 : ℝ) = 4 * M₀ := by ring
  have h2 : 4 * M₀ / (1 / 4 : ℝ) ^ 2 = 64 * M₀ := by ring
  rw [h1] at hd1
  rw [h2] at hd2
  exact ⟨hd1, hd2⟩

/-- **Low-$x$ Set Integral Bound from Half-Plane Boundedness**:
If $f : \mathbb{C} \to \mathbb{C}$ is holomorphic on $\operatorname{UcDisk}$ with
$\|f(z)\| \le M_0$ on $\operatorname{Re} z \le -1/4$, then for any $w \in \operatorname{UcDisk}$,
$$
\left\|\int_{x \in (0, 1/2]} \operatorname{transmuteInnerKernel}(w, x) \,
  \operatorname{transmuteInnerDiff}(f, w, x) \, dx\right\|
  \le 2192 \sqrt{2} \, M_0.
$$ -/
theorem norm_setIntegral_low_transmuteInner_le_of_re_le_bound {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f UcDisk) {M₀ : ℝ} (hM₀_nonneg : 0 ≤ M₀)
    (hM₀ : ∀ z : ℂ, z.re ≤ -1 / 4 → ‖f z‖ ≤ M₀)
    {w : ℂ} (hw : w ∈ UcDisk)
    (h_int : IntegrableOn
      (fun x : ℝ => transmuteInnerKernel w x * transmuteInnerDiff f w x)
      (Ioc (0 : ℝ) (1 / 2)) volume) :
    ‖∫ x in Ioc (0 : ℝ) (1 / 2),
      transmuteInnerKernel w x * transmuteInnerDiff f w x‖ ≤
      2192 * Real.sqrt 2 * M₀ := by
  have h_bd := norm_setIntegral_low_transmuteInner_le hw
    (by positivity : 0 ≤ 4 * M₀) (by positivity : 0 ≤ 64 * M₀) h_int
    (fun x hx => (norm_deriv_and_deriv2_add_log_le_of_re_le hf hM₀ hw hx).1)
    (fun x hx => (norm_deriv_and_deriv2_add_log_le_of_re_le hf hM₀ hw hx).2)
  linarith

/-- **High-$x$ Cauchy Derivative Reduction on Balls of Radius $c (\|1 - e^w\| + (1 - x))$**:
Suppose $f : \mathbb{C} \to \mathbb{C}$ is holomorphic on an open set $U \subseteq \mathbb{C}$
containing $\overline{B}\bigl(w + \log x,\, c (\|1 - e^w\| + 1 - x)\bigr)$ ($c > 0$) and satisfies
$\|f(z)\| \le M \bigl(\|1 - e^w\| + 1 - x\bigr)^{\gamma_{\mathrm{src}}}$ on that closed ball. Then
for $w \in \operatorname{UcDisk}$ with $\operatorname{Im} w \in [-\pi/2, \pi/2]$ and
$x \in [1/2, 1)$,
$$
\|\operatorname{transmuteInnerKernel}(w, x) \, \operatorname{transmuteInnerDiff}(f, w, x)\|
  \le \sqrt{6} \left(\frac{24 M}{c^2} + \frac{20 M}{c}\right)
    (1 - x)^{-1/2} \bigl(\|1 - e^w\| + (1 - x)\bigr)^{\gamma_{\mathrm{src}} - 3/2}.
$$ -/
theorem norm_transmuteInnerKernel_mul_diff_le_of_ball_bound
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    {w : ℂ} (hw : w ∈ UcDisk) (him : w.im ∈ Icc (-π / 2) (π / 2))
    {x : ℝ} (hx : x ∈ Ico (1 / 2 : ℝ) 1)
    {c M γ_src : ℝ} (hc : 0 < c) (hM_nonneg : 0 ≤ M)
    (h_sub : Metric.closedBall (w + (Real.log x : ℂ))
      (c * (‖1 - Complex.exp w‖ + (1 - x))) ⊆ U)
    (hM : ∀ z ∈ Metric.closedBall (w + (Real.log x : ℂ))
      (c * (‖1 - Complex.exp w‖ + (1 - x))),
      ‖f z‖ ≤ M * (‖1 - Complex.exp w‖ + (1 - x)) ^ γ_src) :
    ‖transmuteInnerKernel w x * transmuteInnerDiff f w x‖ ≤
      Real.sqrt 6 * (24 * (M / c ^ 2) + 20 * (M / c)) *
        (1 - x) ^ (-1 / 2 : ℝ) *
        (‖1 - Complex.exp w‖ + (1 - x)) ^ (γ_src - 3 / 2) := by
  set u : ℝ := ‖1 - Complex.exp w‖ + (1 - x)
  have hx1 : 0 < 1 - x := sub_pos.mpr hx.2
  have hu_pos : 0 < u := add_pos_of_nonneg_of_pos (norm_nonneg _) hx1
  have hr_pos : 0 < c * u := mul_pos hc hu_pos
  have hd1_raw := norm_deriv_le_of_ball_bound hU hf hr_pos h_sub hM
  have hd2_raw := norm_deriv2_le_of_ball_bound hU hf hr_pos h_sub hM
  have hd1_eq : (M * u ^ γ_src) / (c * u) = (M / c) * u ^ (γ_src - 1) := by
    have h_rpow : u ^ γ_src / u = u ^ (γ_src - 1) := by
      rw [← Real.rpow_sub_one hu_pos.ne']
    calc
      (M * u ^ γ_src) / (c * u) = (M / c) * (u ^ γ_src / u) := mul_div_mul_comm M (u ^ γ_src) c u
      _ = (M / c) * u ^ (γ_src - 1) := by rw [h_rpow]
  have hd2_eq : 4 * (M * u ^ γ_src) / (c * u) ^ 2 = (4 * M / c ^ 2) * u ^ (γ_src - 2) := by
    have h_rpow : u ^ γ_src / u ^ 2 = u ^ (γ_src - 2) := by
      have hu2 : u ^ (2 : ℕ) = u ^ (2 : ℝ) := (Real.rpow_natCast u 2).symm
      rw [hu2, ← Real.rpow_sub hu_pos]
    calc
      4 * (M * u ^ γ_src) / (c * u) ^ 2
        = ((4 * M) * u ^ γ_src) / (c ^ 2 * u ^ 2) := by rw [← mul_assoc 4 M, mul_pow]
      _ = (4 * M / c ^ 2) * (u ^ γ_src / u ^ 2) := mul_div_mul_comm (4 * M) (u ^ γ_src) (c ^ 2) (u ^ 2)
      _ = (4 * M / c ^ 2) * u ^ (γ_src - 2) := by rw [h_rpow]
  rw [hd1_eq] at hd1_raw
  rw [hd2_eq] at hd2_raw
  have h_main := norm_transmuteInnerKernel_mul_diff_le_of_source_bound hw him hx
    (div_nonneg hM_nonneg hc.le) (by positivity : 0 ≤ 4 * M / c ^ 2) hd1_raw hd2_raw
  have h_coeff : 6 * (4 * M / c ^ 2) + 20 * (M / c) = 24 * (M / c ^ 2) + 20 * (M / c) := by ring
  rwa [h_coeff] at h_main

/-! ## Section 8: Action of `transmuteOpInner` on `block1d H` for All $H \ge 0$

In this section we prove:
1. For $H = 0$, $\operatorname{block1d} 0 z = 1$ and
   $\operatorname{transmuteOpInner}(\operatorname{block1d} 0)(w) = 0$.
2. For all $H > 0$ and $w \in \operatorname{UcDisk}$, integrating by parts on $s \in (0, 1)$
   against the Casimir differential equation for $\operatorname{block1d} H$ and subtracting the
   $s \to 0^+$ counterterm $S_0(H, w, s) = (H - 1/2) e^{H w} s^{H - 1/2}(1 - s)^{1/2}$ shows that
$$
\operatorname{transmuteOpInner}(\operatorname{block1d} H)(w)
  = (\operatorname{transmuteWeight} H : \mathbb{C}) \, e^{H w}.
$$
3. Consequently, for $H > 1/2$, `transmuteOpInner (block1d H) w = transmuteOp (block1d H) w`. -/

/-- For $n \ge 1$, the rising Pochhammer symbol $(0)_{n + 1}$ vanishes. -/
@[simp]
lemma realPochhammer_zero_left_succ (n : ℕ) :
    realPochhammer 0 (n + 1) = 0 := by
  rw [realPochhammer_succ_left, zero_mul]

/-- For $n \ge 1$, the $n$-th series coefficient of $\operatorname{block1d} 0$ vanishes. -/
@[simp]
lemma block1dCoeff_zero_left_succ (n : ℕ) :
    block1dCoeff 0 (n + 1) = 0 := by
  dsimp [block1dCoeff]
  rw [realPochhammer_zero_left_succ, zero_mul, zero_div]

/-- The $H = 0$ (identity) 1D conformal block is identically $1$:
$\operatorname{block1d}(0, z) = 1$ for all $z \in \mathbb{C}$. -/
@[simp]
theorem block1d_zero (z : ℂ) : block1d 0 z = 1 := by
  dsimp [block1d]
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [block1dCoeff_zero_left_succ, Complex.ofReal_zero, zero_mul]

/-- `transmuteOpInner` annihilates the $H = 0$ (identity) conformal block `block1d 0`:
$\operatorname{transmuteOpInner}(\operatorname{block1d} 0)(w) = 0$ for all $w \in \mathbb{C}$. -/
theorem transmuteOpInner_block1d_zero (w : ℂ) :
    transmuteOpInner (block1d 0) w = 0 := by
  have h0 : block1d 0 = fun _ : ℂ => (1 : ℂ) := funext block1d_zero
  rw [h0, transmuteOpInner_const]

/-- The $n$-th term in the series expansion of $\operatorname{block1d}(H, z)$. -/
noncomputable def block1dTerm (H : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  (block1dCoeff H n : ℂ) * Complex.exp (((H + 2 * (n : ℝ) : ℝ) : ℂ) * z)

/-- The $n$-th term in the first derivative series of $\operatorname{block1d}(H, z)$. -/
noncomputable def block1dDeriv1Term (H : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ((block1dCoeff H n * (H + 2 * (n : ℝ)) : ℝ) : ℂ) *
    Complex.exp (((H + 2 * (n : ℝ) : ℝ) : ℂ) * z)

/-- The $n$-th term in the second derivative series of $\operatorname{block1d}(H, z)$. -/
noncomputable def block1dDeriv2Term (H : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ((block1dCoeff H n * (H + 2 * (n : ℝ)) ^ 2 : ℝ) : ℂ) *
    Complex.exp (((H + 2 * (n : ℝ) : ℝ) : ℂ) * z)

/-- Term-by-term first derivative series of $\operatorname{block1d}(H, z)$. -/
noncomputable def block1dDeriv1 (H : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, block1dDeriv1Term H n z

/-- Term-by-term second derivative series of $\operatorname{block1d}(H, z)$. -/
noncomputable def block1dDeriv2 (H : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, block1dDeriv2Term H n z

/-- Summability of $(1 + n)^p e^{\sigma n}$ for any $p \in \mathbb{N}$ and $\sigma < 0$. -/
lemma summable_one_add_natCast_pow_mul_exp (p : ℕ) {σ : ℝ} (hσ : σ < 0) :
    Summable (fun n : ℕ => (1 + (n : ℝ)) ^ p * (Real.exp σ) ^ n) := by
  have h_geom : Summable (fun n : ℕ =>
      (1 + (-σ / (2 * ((p : ℝ) + 1)))⁻¹) ^ p * (Real.exp (σ / 2)) ^ n) := by
    apply Summable.mul_left
    apply summable_geometric_of_lt_one (by positivity)
    rw [Real.exp_lt_one_iff]
    linarith
  exact Summable.of_nonneg_of_le (fun _ => by positivity)
    (fun n => one_add_natCast_pow_mul_exp_le p hσ le_rfl n) h_geom

/-- Norm bound for the $p$-th derivative term of $\operatorname{block1d}(H, z)$ when $H \ge 0$
and $\operatorname{Re} z \le \sigma \le 0$. -/
lemma norm_block1dPowTerm_le {H : ℝ} (hH : 0 ≤ H) (p : ℕ) {σ : ℝ} (hσ : σ ≤ 0)
    {z : ℂ} (hz : z.re ≤ σ) (n : ℕ) :
    ‖((block1dCoeff H n * (H + 2 * (n : ℝ)) ^ p : ℝ) : ℂ) *
        Complex.exp (((H + 2 * (n : ℝ) : ℝ) : ℂ) * z)‖ ≤
      (H + 2) ^ p * ((1 + (n : ℝ)) ^ p * (Real.exp (2 * σ)) ^ n) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h_coeff_nonneg : 0 ≤ block1dCoeff H n * (H + 2 * (n : ℝ)) ^ p :=
    mul_nonneg (block1dCoeff_nonneg hH n) (by positivity)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h_coeff_nonneg, Complex.norm_exp]
  have hre : (((H + 2 * (n : ℝ) : ℝ) : ℂ) * z).re = H * z.re + 2 * (n : ℝ) * z.re := by
    simp [Complex.mul_re]
    ring
  rw [hre, Real.exp_add]
  have hexpH : Real.exp (H * z.re) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have hexp_n : Real.exp (2 * (n : ℝ) * z.re) ≤ (Real.exp (2 * σ)) ^ n := by
    have h_pow : Real.exp (2 * (n : ℝ) * z.re) = (Real.exp (2 * z.re)) ^ n := by
      rw [← Real.exp_nat_mul]
      ring_nf
    rw [h_pow]
    exact pow_le_pow_left₀ (by positivity) (Real.exp_le_exp.mpr (by linarith)) n
  have h_base : H + 2 * (n : ℝ) ≤ (H + 2) * (1 + (n : ℝ)) := by nlinarith
  have h_pow_le : (H + 2 * (n : ℝ)) ^ p ≤ (H + 2) ^ p * (1 + (n : ℝ)) ^ p := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h_base p
  have h_c_le : block1dCoeff H n * (H + 2 * (n : ℝ)) ^ p ≤
      (H + 2) ^ p * (1 + (n : ℝ)) ^ p := by
    calc
      block1dCoeff H n * (H + 2 * (n : ℝ)) ^ p
        ≤ 1 * ((H + 2) ^ p * (1 + (n : ℝ)) ^ p) :=
          mul_le_mul (block1dCoeff_le_one hH n) h_pow_le (by positivity) zero_le_one
      _ = (H + 2) ^ p * (1 + (n : ℝ)) ^ p := one_mul _
  have h_exp_le : Real.exp (H * z.re) * Real.exp (2 * (n : ℝ) * z.re) ≤
      (Real.exp (2 * σ)) ^ n := by
    calc
      Real.exp (H * z.re) * Real.exp (2 * (n : ℝ) * z.re)
        ≤ 1 * (Real.exp (2 * σ)) ^ n :=
          mul_le_mul hexpH hexp_n (by positivity) zero_le_one
      _ = (Real.exp (2 * σ)) ^ n := one_mul _
  calc
    block1dCoeff H n * (H + 2 * (n : ℝ)) ^ p *
        (Real.exp (H * z.re) * Real.exp (2 * (n : ℝ) * z.re))
      ≤ ((H + 2) ^ p * (1 + (n : ℝ)) ^ p) * (Real.exp (2 * σ)) ^ n :=
        mul_le_mul h_c_le h_exp_le (by positivity) (by positivity)
    _ = (H + 2) ^ p * ((1 + (n : ℝ)) ^ p * (Real.exp (2 * σ)) ^ n) := by ring

lemma summable_block1dTerm {H : ℝ} (hH : 0 ≤ H) {z : ℂ} (hz : z ∈ UcDisk) :
    Summable (fun n : ℕ => block1dTerm H n z) :=
  summable_block1d hH (mem_UcDisk_iff.mp hz)

lemma summable_block1dDeriv1Term {H : ℝ} (hH : 0 ≤ H) {z : ℂ} (hz : z ∈ UcDisk) :
    Summable (fun n : ℕ => block1dDeriv1Term H n z) := by
  have hz_re : z.re < 0 := mem_UcDisk_iff.mp hz
  have h_dom := (summable_one_add_natCast_pow_mul_exp 1 (by linarith : 2 * z.re < 0)).mul_left
    ((H + 2) ^ 1)
  refine Summable.of_norm_bounded h_dom fun n => ?_
  simpa [block1dDeriv1Term, pow_one] using
    norm_block1dPowTerm_le hH 1 hz_re.le le_rfl n

lemma summable_block1dDeriv2Term {H : ℝ} (hH : 0 ≤ H) {z : ℂ} (hz : z ∈ UcDisk) :
    Summable (fun n : ℕ => block1dDeriv2Term H n z) := by
  have hz_re : z.re < 0 := mem_UcDisk_iff.mp hz
  have h_dom := (summable_one_add_natCast_pow_mul_exp 2 (by linarith : 2 * z.re < 0)).mul_left
    ((H + 2) ^ 2)
  refine Summable.of_norm_bounded h_dom fun n => ?_
  simpa [block1dDeriv2Term] using
    norm_block1dPowTerm_le hH 2 hz_re.le le_rfl n

lemma hasDerivAt_block1dTerm (H : ℝ) (n : ℕ) (z : ℂ) :
    HasDerivAt (block1dTerm H n) (block1dDeriv1Term H n z) z := by
  have h1 : HasDerivAt (fun w : ℂ => ((H + 2 * (n : ℝ) : ℝ) : ℂ) * w)
      ((H + 2 * (n : ℝ) : ℝ) : ℂ) z := by
    simpa using (hasDerivAt_id z).const_mul ((H + 2 * (n : ℝ) : ℝ) : ℂ)
  have h2 := h1.cexp.const_mul (block1dCoeff H n : ℂ)
  refine h2.congr_deriv ?_
  dsimp [block1dDeriv1Term]
  push_cast
  ring

lemma hasDerivAt_block1dDeriv1Term (H : ℝ) (n : ℕ) (z : ℂ) :
    HasDerivAt (block1dDeriv1Term H n) (block1dDeriv2Term H n z) z := by
  have h1 : HasDerivAt (fun w : ℂ => ((H + 2 * (n : ℝ) : ℝ) : ℂ) * w)
      ((H + 2 * (n : ℝ) : ℝ) : ℂ) z := by
    simpa using (hasDerivAt_id z).const_mul ((H + 2 * (n : ℝ) : ℝ) : ℂ)
  have h2 := h1.cexp.const_mul ((block1dCoeff H n * (H + 2 * (n : ℝ)) : ℝ) : ℂ)
  refine h2.congr_deriv ?_
  dsimp [block1dDeriv2Term]
  push_cast
  ring

/-- For $z \in \operatorname{UcDisk}$ and $y \in B(z, -\operatorname{Re} z / 2)$, we have
$\operatorname{Re} y \le \operatorname{Re} z / 2$. -/
lemma re_le_half_of_mem_ball {z y : ℂ} (hy : y ∈ Metric.ball z (-z.re / 2)) :
    y.re ≤ z.re / 2 := by
  rw [Metric.mem_ball, Complex.dist_eq] at hy
  have h1 : (y - z).re ≤ ‖y - z‖ := Complex.re_le_norm (y - z)
  have h2 : (y - z).re = y.re - z.re := Complex.sub_re y z
  linarith

/-- Term-by-term differentiation of `block1d H` on `UcDisk`. -/
theorem hasDerivAt_block1d {H : ℝ} (hH : 0 ≤ H) {z : ℂ} (hz : z ∈ UcDisk) :
    HasDerivAt (block1d H) (block1dDeriv1 H z) z := by
  have hz_re : z.re < 0 := mem_UcDisk_iff.mp hz
  set t : Set ℂ := Metric.ball z (-z.re / 2)
  have hr : 0 < -z.re / 2 := by linarith
  have h_sum : Summable (fun n : ℕ =>
      (H + 2) ^ 1 * ((1 + (n : ℝ)) ^ 1 * (Real.exp z.re) ^ n)) :=
    (summable_one_add_natCast_pow_mul_exp 1 hz_re).mul_left ((H + 2) ^ 1)
  have h_bd : ∀ n : ℕ, ∀ y ∈ t, ‖block1dDeriv1Term H n y‖ ≤
      (H + 2) ^ 1 * ((1 + (n : ℝ)) ^ 1 * (Real.exp z.re) ^ n) := by
    intro n y hy
    have hy_re : y.re ≤ z.re / 2 := re_le_half_of_mem_ball hy
    have h_eq : 2 * (z.re / 2) = z.re := by ring
    rw [← h_eq]
    simpa [block1dDeriv1Term, pow_one] using
      norm_block1dPowTerm_le hH 1 (by linarith : z.re / 2 ≤ 0) hy_re n
  exact hasDerivAt_tsum_of_isPreconnected h_sum Metric.isOpen_ball
    (convex_ball z (-z.re / 2)).isPreconnected
    (fun n y _ => hasDerivAt_block1dTerm H n y) h_bd
    (Metric.mem_ball_self hr) (summable_block1dTerm hH hz) (Metric.mem_ball_self hr)

theorem deriv_block1d {H : ℝ} (hH : 0 ≤ H) {z : ℂ} (hz : z ∈ UcDisk) :
    deriv (block1d H) z = block1dDeriv1 H z :=
  (hasDerivAt_block1d hH hz).deriv

/-- Term-by-term differentiation of `block1dDeriv1 H` on `UcDisk`. -/
theorem hasDerivAt_block1dDeriv1 {H : ℝ} (hH : 0 ≤ H) {z : ℂ} (hz : z ∈ UcDisk) :
    HasDerivAt (block1dDeriv1 H) (block1dDeriv2 H z) z := by
  have hz_re : z.re < 0 := mem_UcDisk_iff.mp hz
  set t : Set ℂ := Metric.ball z (-z.re / 2)
  have hr : 0 < -z.re / 2 := by linarith
  have h_sum : Summable (fun n : ℕ =>
      (H + 2) ^ 2 * ((1 + (n : ℝ)) ^ 2 * (Real.exp z.re) ^ n)) :=
    (summable_one_add_natCast_pow_mul_exp 2 hz_re).mul_left ((H + 2) ^ 2)
  have h_bd : ∀ n : ℕ, ∀ y ∈ t, ‖block1dDeriv2Term H n y‖ ≤
      (H + 2) ^ 2 * ((1 + (n : ℝ)) ^ 2 * (Real.exp z.re) ^ n) := by
    intro n y hy
    have hy_re : y.re ≤ z.re / 2 := re_le_half_of_mem_ball hy
    have h_eq : 2 * (z.re / 2) = z.re := by ring
    rw [← h_eq]
    simpa [block1dDeriv2Term] using
      norm_block1dPowTerm_le hH 2 (by linarith : z.re / 2 ≤ 0) hy_re n
  exact hasDerivAt_tsum_of_isPreconnected h_sum Metric.isOpen_ball
    (convex_ball z (-z.re / 2)).isPreconnected
    (fun n y _ => hasDerivAt_block1dDeriv1Term H n y) h_bd
    (Metric.mem_ball_self hr) (summable_block1dDeriv1Term hH hz) (Metric.mem_ball_self hr)

theorem deriv_deriv_block1d {H : ℝ} (hH : 0 ≤ H) {z : ℂ} (hz : z ∈ UcDisk) :
    deriv (deriv (block1d H)) z = block1dDeriv2 H z := by
  have h_ev : deriv (block1d H) =ᶠ[𝓝 z] block1dDeriv1 H :=
    Filter.eventuallyEq_of_mem (isOpen_UcDisk.mem_nhds hz) fun w hw => deriv_block1d hH hw
  rw [h_ev.deriv_eq, (hasDerivAt_block1dDeriv1 hH hz).deriv]

/-- Two-term Casimir recurrence for `block1dCoeff`:
$$
c_{n + 1}(H) \bigl((H + 2(n + 1))^2 - (H + 2(n + 1)) - H(H - 1)\bigr)
  = c_n(H) \bigl((H + 2n)^2 + (H + 2n) - H(H - 1)\bigr).
$$ -/
lemma block1dCoeff_casimir_succ {H : ℝ} (hH : 0 ≤ H) (n : ℕ) :
    block1dCoeff H (n + 1) *
        ((H + 2 * ((n + 1 : ℕ) : ℝ)) ^ 2 - (H + 2 * ((n + 1 : ℕ) : ℝ)) - H * (H - 1)) =
      block1dCoeff H n *
        ((H + 2 * (n : ℝ)) ^ 2 + (H + 2 * (n : ℝ)) - H * (H - 1)) := by
  dsimp [block1dCoeff]
  rw [realPochhammer_succ H n, realPochhammer_succ (1 / 2) n,
    realPochhammer_succ (H + 1 / 2) n, Nat.factorial_succ]
  push_cast
  have h1 : realPochhammer (H + 1 / 2) n ≠ 0 := (realPochhammer_pos (by linarith) n).ne'
  have h2 : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have h3 : H + 1 / 2 + (n : ℝ) ≠ 0 := by positivity
  have h4 : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [h1, h2, h3, h4]
  ring

/-- **1D Casimir Differential Equation for `block1d H` on `UcDisk`**:
For all $H \ge 0$ and $z \in \operatorname{UcDisk}$,
$$
(1 - e^{2z}) (\operatorname{block1d} H)''(z) - (1 + e^{2z}) (\operatorname{block1d} H)'(z)
  = H(H - 1) (1 - e^{2z}) \operatorname{block1d}(H, z).
$$ -/
theorem casimir_block1d {H : ℝ} (hH : 0 ≤ H) {z : ℂ} (hz : z ∈ UcDisk) :
    (1 - Complex.exp (2 * z)) * block1dDeriv2 H z -
        (1 + Complex.exp (2 * z)) * block1dDeriv1 H z =
      ((H * (H - 1) : ℝ) : ℂ) * (1 - Complex.exp (2 * z)) * block1d H z := by
  set a : ℕ → ℂ := fun n =>
    block1dDeriv2Term H n z - block1dDeriv1Term H n z -
      ((H * (H - 1) : ℝ) : ℂ) * block1dTerm H n z
  set b : ℕ → ℂ := fun n =>
    block1dDeriv2Term H n z + block1dDeriv1Term H n z -
      ((H * (H - 1) : ℝ) : ℂ) * block1dTerm H n z
  have hs0 := summable_block1dTerm hH hz
  have hs1 := summable_block1dDeriv1Term hH hz
  have hs2 := summable_block1dDeriv2Term hH hz
  have hsa : Summable a := (hs2.sub hs1).sub (hs0.mul_left _)
  have hsb : Summable b := (hs2.add hs1).sub (hs0.mul_left _)
  have ha0 : a 0 = 0 := by
    dsimp [a, block1dDeriv2Term, block1dDeriv1Term, block1dTerm]
    push_cast
    ring
  have ha_succ : ∀ n : ℕ, a (n + 1) = Complex.exp (2 * z) * b n := by
    intro n
    dsimp [a, b, block1dDeriv2Term, block1dDeriv1Term, block1dTerm]
    have h_rec := congrArg (fun r : ℝ => (r : ℂ)) (block1dCoeff_casimir_succ hH n)
    have h_exp : Complex.exp (((H + 2 * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) * z) =
        Complex.exp (2 * z) * Complex.exp (((H + 2 * (n : ℝ) : ℝ) : ℂ) * z) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [h_exp]
    have h_lhs :
        ((block1dCoeff H (n + 1) * (H + 2 * ((n + 1 : ℕ) : ℝ)) ^ 2 : ℝ) : ℂ) *
            (Complex.exp (2 * z) * Complex.exp (((H + 2 * (n : ℝ) : ℝ) : ℂ) * z)) -
          ((block1dCoeff H (n + 1) * (H + 2 * ((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ) *
            (Complex.exp (2 * z) * Complex.exp (((H + 2 * (n : ℝ) : ℝ) : ℂ) * z)) -
          ((H * (H - 1) : ℝ) : ℂ) *
            ((block1dCoeff H (n + 1) : ℂ) *
              (Complex.exp (2 * z) * Complex.exp (((H + 2 * (n : ℝ) : ℝ) : ℂ) * z))) =
        ((block1dCoeff H (n + 1) *
          ((H + 2 * ((n + 1 : ℕ) : ℝ)) ^ 2 - (H + 2 * ((n + 1 : ℕ) : ℝ)) -
            H * (H - 1)) : ℝ) : ℂ) *
          Complex.exp (2 * z) * Complex.exp (((H + 2 * (n : ℝ) : ℝ) : ℂ) * z) := by
      push_cast
      ring
    rw [h_lhs, h_rec]
    push_cast
    ring
  have h_tsum_a : (∑' n : ℕ, a n) = Complex.exp (2 * z) * (∑' n : ℕ, b n) := by
    rw [hsa.tsum_eq_zero_add, ha0, zero_add]
    simp_rw [ha_succ, tsum_mul_left]
  have h_eval_a : (∑' n : ℕ, a n) =
      block1dDeriv2 H z - block1dDeriv1 H z -
        ((H * (H - 1) : ℝ) : ℂ) * block1d H z := by
    dsimp [a]
    rw [Summable.tsum_sub (hs2.sub hs1) (hs0.mul_left _),
      Summable.tsum_sub hs2 hs1, tsum_mul_left]
    rfl
  have h_eval_b : (∑' n : ℕ, b n) =
      block1dDeriv2 H z + block1dDeriv1 H z -
        ((H * (H - 1) : ℝ) : ℂ) * block1d H z := by
    dsimp [b]
    rw [Summable.tsum_sub (hs2.add hs1) (hs0.mul_left _),
      Summable.tsum_add hs2 hs1, tsum_mul_left]
    rfl
  rw [h_eval_a, h_eval_b] at h_tsum_a
  linear_combination h_tsum_a

/-- The kernel weight $W(w, s) = s^{-1/2} (1 - s)^{1/2} (1 - s e^{2w})^{1/2}$ appearing in the
integration-by-parts boundary term for `transmuteOpInner`. -/
noncomputable def transmuteBoundaryKernel (w : ℂ) (s : ℝ) : ℂ :=
  ((s ^ (-1 / 2 : ℝ) * (1 - s) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
    (1 - (s : ℂ) * Complex.exp (2 * w)) ^ (1 / 2 : ℂ)

/-- The unregularized integration-by-parts boundary term for `block1d H`:
$$
B(H, w, s) = W(w, s) \left[\frac{1 + s e^w}{1 - s e^w} (\operatorname{block1d} H)'(w + \log s)
  - \frac{1}{2} \operatorname{block1d}(H, w + \log s)\right].
$$ -/
noncomputable def transmuteBoundaryTerm (H : ℝ) (w : ℂ) (s : ℝ) : ℂ :=
  transmuteBoundaryKernel w s *
    ((1 + (s : ℂ) * Complex.exp w) / (1 - (s : ℂ) * Complex.exp w) *
      block1dDeriv1 H (w + (Real.log s : ℂ)) -
      (1 / 2 : ℂ) * block1d H (w + (Real.log s : ℂ)))

/-- The leading $s \to 0^+$ asymptotic counterterm
$$S_0(H, w, s) = \left(H - \frac{1}{2}\right) e^{H w} s^{H - 1/2} (1 - s)^{1/2}.$$ -/
noncomputable def transmuteBoundarySub (H : ℝ) (w : ℂ) (s : ℝ) : ℂ :=
  ((H - 1 / 2 : ℝ) : ℂ) * Complex.exp ((H : ℂ) * w) *
    ((s ^ (H - 1 / 2 : ℝ) * (1 - s) ^ (1 / 2 : ℝ) : ℝ) : ℂ)

/-- The regularized boundary term $\widetilde{B}(H, w, s) = B(H, w, s) - S_0(H, w, s)$, which
vanishes at both endpoints $s \to 0^+$ and $s \to 1^-$ for all $H > 0$. -/
noncomputable def transmuteRegBoundary (H : ℝ) (w : ℂ) (s : ℝ) : ℂ :=
  transmuteBoundaryTerm H w s - transmuteBoundarySub H w s

/-- For $w \in \operatorname{UcDisk}$ and $s \in [0, 1]$, we have
$1 - s e^{2w} \in \operatorname{slitPlane}$. -/
lemma one_sub_mul_exp_two_mul_mem_slitPlane {w : ℂ} (hw : w ∈ UcDisk)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    1 - (s : ℂ) * Complex.exp (2 * w) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  have h_norm : ‖(s : ℂ) * Complex.exp (2 * w)‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.1, Complex.norm_exp]
    have hre : (2 * w).re = 2 * w.re := by simp [Complex.mul_re]
    have hexp : Real.exp ((2 * w).re) < 1 := by
      rw [hre, Real.exp_lt_one_iff]
      linarith [mem_UcDisk_iff.mp hw]
    nlinarith [hs.1, hs.2, Real.exp_pos ((2 * w).re)]
  have hre_le : ((s : ℂ) * Complex.exp (2 * w)).re ≤ ‖(s : ℂ) * Complex.exp (2 * w)‖ :=
    Complex.re_le_norm _
  simp only [Complex.sub_re, Complex.one_re]
  linarith

/-- Algebraic relation between `transmuteBoundaryKernel` and `transmuteInnerKernel` on
`Ioo 0 1`. -/
lemma transmuteBoundaryKernel_eq_mul_transmuteInnerKernel {w : ℂ} (hw : w ∈ UcDisk)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    transmuteBoundaryKernel w s =
      transmuteInnerKernel w s * (1 - (s : ℂ)) *
        (1 - (s : ℂ) * Complex.exp (2 * w)) := by
  dsimp [transmuteBoundaryKernel, transmuteInnerKernel]
  have hs1 : 0 < 1 - s := sub_pos.mpr hs.2
  have h_rpow : (1 - s) ^ (-1 / 2 : ℝ) * (1 - s) = (1 - s) ^ (1 / 2 : ℝ) := by
    have h1 := (Real.rpow_add_one hs1.ne' (-1 / 2 : ℝ)).symm
    have h2 : (-1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
    rw [h2] at h1
    exact h1
  have hz_ne : 1 - (s : ℂ) * Complex.exp (2 * w) ≠ 0 :=
    Complex.slitPlane_ne_zero
      (one_sub_mul_exp_two_mul_mem_slitPlane hw ⟨hs.1.le, hs.2.le⟩)
  have h_cpow :
      (1 - (s : ℂ) * Complex.exp (2 * w)) ^ (-1 / 2 : ℂ) *
        (1 - (s : ℂ) * Complex.exp (2 * w)) =
      (1 - (s : ℂ) * Complex.exp (2 * w)) ^ (1 / 2 : ℂ) := by
    have h1 := (Complex.cpow_add (-1 / 2 : ℂ) (1 : ℂ) hz_ne).symm
    rw [Complex.cpow_one] at h1
    have h2 : (-1 / 2 : ℂ) + 1 = (1 / 2 : ℂ) := by norm_num
    rw [h2] at h1
    exact h1
  rw [← h_rpow, ← h_cpow]
  push_cast
  ring

/-- Derivative of `transmuteBoundaryKernel w` on $s \in (0, 1)$:
$$
\frac{d}{ds} W(w, s)
  = -\operatorname{transmuteInnerKernel}(w, s) \, \frac{1 - s^2 e^{2w}}{2 s}.
$$ -/
lemma hasDerivAt_transmuteBoundaryKernel {w : ℂ} (hw : w ∈ UcDisk)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (transmuteBoundaryKernel w)
      (-transmuteInnerKernel w s *
        (1 - ((s ^ 2 : ℝ) : ℂ) * Complex.exp (2 * w)) / (2 * (s : ℂ))) s := by
  have hs0 : 0 < s := hs.1
  have hs1 : 0 < 1 - s := sub_pos.mpr hs.2
  have hd_s : HasDerivAt (fun x : ℝ => x ^ (-1 / 2 : ℝ))
      ((-1 / 2 : ℝ) * (s ^ (-1 / 2 : ℝ) * s⁻¹)) s := by
    have h1 := Real.hasDerivAt_rpow_const (p := (-1 / 2 : ℝ)) (x := s) (Or.inl hs0.ne')
    refine h1.congr_deriv ?_
    have h_exp : s ^ ((-1 / 2 : ℝ) - 1) = s ^ (-1 / 2 : ℝ) * s⁻¹ := by
      rw [Real.rpow_sub_one hs0.ne']
      ring
    rw [h_exp]
  have hd_1s : HasDerivAt (fun x : ℝ => (1 - x) ^ (1 / 2 : ℝ))
      ((-1 / 2 : ℝ) * (1 - s) ^ (-1 / 2 : ℝ)) s := by
    have h_in : HasDerivAt (fun x : ℝ => 1 - x) (-1 : ℝ) s := by
      have h0 := (hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)
      exact h0.congr_deriv (by ring)
    have h1 := h_in.rpow_const (p := (1 / 2 : ℝ)) (Or.inl hs1.ne')
    refine h1.congr_deriv ?_
    have h_exp : (1 / 2 : ℝ) - 1 = -1 / 2 := by norm_num
    rw [h_exp]
    ring
  have hd_real : HasDerivAt
      (fun x : ℝ => ((x ^ (-1 / 2 : ℝ) * (1 - x) ^ (1 / 2 : ℝ) : ℝ) : ℂ))
      (((((-1 / 2 : ℝ) * (s ^ (-1 / 2 : ℝ) * s⁻¹)) * (1 - s) ^ (1 / 2 : ℝ) +
        s ^ (-1 / 2 : ℝ) * ((-1 / 2 : ℝ) * (1 - s) ^ (-1 / 2 : ℝ)) : ℝ) : ℂ)) s :=
    (hd_s.mul hd_1s).ofReal_comp
  have hd_in_c : HasDerivAt
      (fun x : ℝ => 1 - (x : ℂ) * Complex.exp (2 * w))
      (-Complex.exp (2 * w)) s := by
    have h1 : HasDerivAt (fun x : ℝ => (x : ℂ) * Complex.exp (2 * w))
        ((1 : ℂ) * Complex.exp (2 * w)) s :=
      (Complex.ofRealCLM.hasDerivAt).mul_const (Complex.exp (2 * w))
    have h0 := (hasDerivAt_const s (1 : ℂ)).sub h1
    exact h0.congr_deriv (by ring)
  have h_slit : 1 - (s : ℂ) * Complex.exp (2 * w) ∈ Complex.slitPlane :=
    one_sub_mul_exp_two_mul_mem_slitPlane hw ⟨hs.1.le, hs.2.le⟩
  have hd_cpow : HasDerivAt
      (fun x : ℝ => (1 - (x : ℂ) * Complex.exp (2 * w)) ^ (1 / 2 : ℂ))
      ((1 / 2 : ℂ) * (1 - (s : ℂ) * Complex.exp (2 * w)) ^ (-1 / 2 : ℂ) *
        (-Complex.exp (2 * w))) s := by
    have h1 := (Complex.hasStrictDerivAt_cpow_const (c := (1 / 2 : ℂ)) h_slit).hasDerivAt.comp
      s hd_in_c
    refine h1.congr_deriv ?_
    have h_exp : (1 / 2 : ℂ) - 1 = (-1 / 2 : ℂ) := by norm_num
    rw [h_exp]
  have hd_prod := hd_real.mul hd_cpow
  refine hd_prod.congr_deriv ?_
  have h_rpow : (1 - s) ^ (1 / 2 : ℝ) = (1 - s) ^ (-1 / 2 : ℝ) * (1 - s) := by
    have h1 := Real.rpow_add_one hs1.ne' (-1 / 2 : ℝ)
    have h2 : (-1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
    rw [h2] at h1
    exact h1
  have hz_ne : 1 - (s : ℂ) * Complex.exp (2 * w) ≠ 0 :=
    Complex.slitPlane_ne_zero h_slit
  have h_cpow :
      (1 - (s : ℂ) * Complex.exp (2 * w)) ^ (1 / 2 : ℂ) =
        (1 - (s : ℂ) * Complex.exp (2 * w)) ^ (-1 / 2 : ℂ) *
          (1 - (s : ℂ) * Complex.exp (2 * w)) := by
    have h1 := Complex.cpow_add (-1 / 2 : ℂ) (1 : ℂ) hz_ne
    rw [Complex.cpow_one] at h1
    have h2 : (-1 / 2 : ℂ) + 1 = (1 / 2 : ℂ) := by norm_num
    rw [h2] at h1
    exact h1
  dsimp [transmuteInnerKernel]
  rw [h_rpow, h_cpow]
  have hs_ne : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs0.ne'
  push_cast
  field_simp [hs_ne]
  ring

/-- **Pointwise Integration-by-Parts Identity for `block1d H`**:
For all $H \ge 0$, $w \in \operatorname{UcDisk}$, and $s \in (0, 1)$,
$$
\frac{d}{ds} B(H, w, s)
  = \left(H - \frac{1}{2}\right)^2 \operatorname{transmuteKernel}(w, s) \,
      \operatorname{block1d}(H, w + \log s)
    - \operatorname{transmuteInnerKernel}(w, s) \,
      \operatorname{transmuteInnerDiff}(\operatorname{block1d} H, w, s).
$$ -/
theorem hasDerivAt_transmuteBoundaryTerm {H : ℝ} (hH : 0 ≤ H) {w : ℂ} (hw : w ∈ UcDisk)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (transmuteBoundaryTerm H w)
      (((H - 1 / 2 : ℝ) : ℂ) ^ 2 * transmuteKernel w s *
          block1d H (w + (Real.log s : ℂ)) -
        transmuteInnerKernel w s * transmuteInnerDiff (block1d H) w s) s := by
  have hs0 : 0 < s := hs.1
  have hs_ne : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs0.ne'
  set z : ℂ := w + (Real.log s : ℂ)
  have hz : z ∈ UcDisk := by
    rw [mem_UcDisk_iff]
    have hlog : Real.log s < 0 := Real.log_neg hs.1 hs.2
    have hre : z.re = w.re + Real.log s := by simp [z, Complex.add_re]
    linarith [mem_UcDisk_iff.mp hw]
  have hd_log : HasDerivAt (fun x : ℝ => w + (Real.log x : ℂ)) ((s : ℂ)⁻¹) s := by
    have h1 := (Real.hasDerivAt_log hs0.ne').ofReal_comp
    have h0 := (hasDerivAt_const s w).add h1
    exact h0.congr_deriv (by simp)
  have hd_b0 : HasDerivAt (fun x : ℝ => block1d H (w + (Real.log x : ℂ)))
      (block1dDeriv1 H z * (s : ℂ)⁻¹) s :=
    HasDerivAt.comp (h₂ := block1d H) (h := fun x : ℝ => w + (Real.log x : ℂ))
      s (hasDerivAt_block1d hH hz) hd_log
  have hd_b1 : HasDerivAt (fun x : ℝ => block1dDeriv1 H (w + (Real.log x : ℂ)))
      (block1dDeriv2 H z * (s : ℂ)⁻¹) s :=
    HasDerivAt.comp (h₂ := block1dDeriv1 H) (h := fun x : ℝ => w + (Real.log x : ℂ))
      s (hasDerivAt_block1dDeriv1 hH hz) hd_log
  have hz_sub : 1 - (s : ℂ) * Complex.exp w ≠ 0 := one_sub_mul_exp_ne_zero hw hs
  have hd_rat : HasDerivAt
      (fun x : ℝ => (1 + (x : ℂ) * Complex.exp w) / (1 - (x : ℂ) * Complex.exp w))
      (2 * Complex.exp w / (1 - (s : ℂ) * Complex.exp w) ^ 2) s := by
    have h_lin : HasDerivAt (fun x : ℝ => (x : ℂ) * Complex.exp w)
        ((1 : ℂ) * Complex.exp w) s :=
      (Complex.ofRealCLM.hasDerivAt).mul_const (Complex.exp w)
    have h1 : HasDerivAt (fun x : ℝ => 1 + (x : ℂ) * Complex.exp w) (Complex.exp w) s :=
      ((hasDerivAt_const s (1 : ℂ)).add h_lin).congr_deriv (by ring)
    have h2 : HasDerivAt (fun x : ℝ => 1 - (x : ℂ) * Complex.exp w) (-Complex.exp w) s :=
      ((hasDerivAt_const s (1 : ℂ)).sub h_lin).congr_deriv (by ring)
    exact (h1.div h2 hz_sub).congr_deriv (by ring)
  have hd_inner : HasDerivAt
      (fun x : ℝ =>
        (1 + (x : ℂ) * Complex.exp w) / (1 - (x : ℂ) * Complex.exp w) *
          block1dDeriv1 H (w + (Real.log x : ℂ)) -
          (1 / 2 : ℂ) * block1d H (w + (Real.log x : ℂ)))
      ((2 * Complex.exp w / (1 - (s : ℂ) * Complex.exp w) ^ 2) * block1dDeriv1 H z +
        ((1 + (s : ℂ) * Complex.exp w) / (1 - (s : ℂ) * Complex.exp w)) *
          (block1dDeriv2 H z * (s : ℂ)⁻¹) -
        (1 / 2 : ℂ) * (block1dDeriv1 H z * (s : ℂ)⁻¹)) s :=
    (hd_rat.mul hd_b1).sub (hd_b0.const_mul (1 / 2 : ℂ))
  have hd_B := (hasDerivAt_transmuteBoundaryKernel hw hs).mul hd_inner
  refine hd_B.congr_deriv ?_
  rw [transmuteBoundaryKernel_eq_mul_transmuteInnerKernel hw hs]
  have h_d1 : deriv (block1d H) z = block1dDeriv1 H z := deriv_block1d hH hz
  have h_d2 : deriv (deriv (block1d H)) z = block1dDeriv2 H z := deriv_deriv_block1d hH hz
  have h_cas := casimir_block1d hH hz
  have hexp_2z : Complex.exp (2 * z) = ((s ^ 2 : ℝ) : ℂ) * Complex.exp (2 * w) := by
    have h1 : 2 * z = 2 * w + 2 * (Real.log s : ℂ) := by dsimp [z]; ring
    rw [h1, Complex.exp_add, mul_comm, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul,
      ← Complex.ofReal_exp]
    have h2 : Real.exp (2 * Real.log s) = s ^ 2 := by
      rw [mul_comm, ← Real.rpow_def_of_pos hs0, Real.rpow_two]
    rw [h2]
  rw [hexp_2z] at h_cas
  have h_exp_2w : Complex.exp (2 * w) = (Complex.exp w) ^ 2 := by
    rw [← Complex.exp_nat_mul]
    congr 1
  have h_tk : transmuteKernel w s =
      transmuteInnerKernel w s *
        (1 - ((s ^ 2 : ℝ) : ℂ) * Complex.exp (2 * w)) * (s : ℂ)⁻¹ := by
    dsimp [transmuteKernel, transmuteInnerKernel]
    have h_s : s ^ (-3 / 2 : ℝ) = s ^ (-1 / 2 : ℝ) * s⁻¹ := by
      have h1 := Real.rpow_sub_one hs0.ne' (-1 / 2 : ℝ)
      have h2 : (-1 / 2 : ℝ) - 1 = -3 / 2 := by norm_num
      rw [h2] at h1
      exact h1
    rw [h_s]
    push_cast
    ring
  dsimp [transmuteInnerDiff]
  have hz_def : w + (Real.log s : ℂ) = z := rfl
  rw [hz_def, h_d1, h_d2, h_tk, h_exp_2w]
  rw [h_exp_2w] at h_cas
  set K := transmuteInnerKernel w s
  set F0 := block1d H z
  set F1 := block1dDeriv1 H z
  set F2 := block1dDeriv2 H z
  set q := Complex.exp w
  have hq_sub : 1 - (s : ℂ) * q ≠ 0 := hz_sub
  push_cast at h_cas ⊢
  have h_alg :
      (-K * (1 - (s : ℂ) ^ 2 * q ^ 2) / (2 * (s : ℂ)) *
          ((1 + (s : ℂ) * q) / (1 - (s : ℂ) * q) * F1 - 1 / 2 * F0) +
        K * (1 - (s : ℂ)) * (1 - (s : ℂ) * q ^ 2) *
          (2 * q / (1 - (s : ℂ) * q) ^ 2 * F1 +
            (1 + (s : ℂ) * q) / (1 - (s : ℂ) * q) * (F2 * (s : ℂ)⁻¹) -
            1 / 2 * (F1 * (s : ℂ)⁻¹))) -
        (((H : ℂ) - 1 / 2) ^ 2 * (K * (1 - (s : ℂ) ^ 2 * q ^ 2) * (s : ℂ)⁻¹) * F0 -
          K * ((1 - q) ^ 2 *
            ((1 + (s : ℂ) * q) / (1 - (s : ℂ) * q) * F2 +
              2 * (s : ℂ) * q / (1 - (s : ℂ) * q) ^ 2 * F1) -
            1 / 2 * (1 + q) ^ 2 * F1)) =
      K * (s : ℂ)⁻¹ *
        (((1 - (s : ℂ) ^ 2 * q ^ 2) * F2 - (1 + (s : ℂ) ^ 2 * q ^ 2) * F1) -
          (H : ℂ) * ((H : ℂ) - 1) * (1 - (s : ℂ) ^ 2 * q ^ 2) * F0) := by
    field_simp [hs_ne, hq_sub]
    ring
  linear_combination h_alg + K * (s : ℂ)⁻¹ * h_cas

/-- Derivative of the counterterm $S_0(H, w, s)$ on $s \in (0, 1)$:
$$
\frac{d}{ds} S_0(H, w, s)
  = e^{H w} \left[\left(H - \frac{1}{2}\right)^2 \operatorname{betaKernel}(H, 0, s)
    - H\left(H - \frac{1}{2}\right) \operatorname{betaKernel}(H, 1, s)\right].
$$ -/
lemma hasDerivAt_transmuteBoundarySub (H : ℝ) (w : ℂ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (transmuteBoundarySub H w)
      (Complex.exp ((H : ℂ) * w) *
        (((H - 1 / 2 : ℝ) : ℂ) ^ 2 * (betaKernel H 0 s : ℂ) -
          ((H * (H - 1 / 2) : ℝ) : ℂ) * (betaKernel H 1 s : ℂ))) s := by
  have hs0 : 0 < s := hs.1
  have hs1 : 0 < 1 - s := sub_pos.mpr hs.2
  have hd1 : HasDerivAt (fun x : ℝ => x ^ (H - 1 / 2 : ℝ))
      ((H - 1 / 2 : ℝ) * s ^ (H - 3 / 2 : ℝ)) s := by
    have h1 := Real.hasDerivAt_rpow_const (p := H - 1 / 2) (x := s) (Or.inl hs0.ne')
    refine h1.congr_deriv ?_
    have h_exp : H - 1 / 2 - 1 = H - 3 / 2 := by ring
    rw [h_exp]
  have hd2 : HasDerivAt (fun x : ℝ => (1 - x) ^ (1 / 2 : ℝ))
      ((-1 / 2 : ℝ) * (1 - s) ^ (-1 / 2 : ℝ)) s := by
    have h_in : HasDerivAt (fun x : ℝ => 1 - x) (-1 : ℝ) s := by
      have h0 := (hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)
      exact h0.congr_deriv (by ring)
    have h1 := h_in.rpow_const (p := (1 / 2 : ℝ)) (Or.inl hs1.ne')
    refine h1.congr_deriv ?_
    have h_exp : (1 / 2 : ℝ) - 1 = -1 / 2 := by norm_num
    rw [h_exp]
    ring
  have hd_prod := ((hd1.mul hd2).ofReal_comp).const_mul
    (((H - 1 / 2 : ℝ) : ℂ) * Complex.exp ((H : ℂ) * w))
  refine hd_prod.congr_deriv ?_
  have h_1s : (1 - s) ^ (1 / 2 : ℝ) = (1 - s) ^ (-1 / 2 : ℝ) * (1 - s) := by
    have h1 := Real.rpow_add_one hs1.ne' (-1 / 2 : ℝ)
    have h2 : (-1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
    rw [h2] at h1
    exact h1
  have h_s : s ^ (H - 3 / 2 : ℝ) * s = s ^ (H - 1 / 2 : ℝ) := by
    have h1 := (Real.rpow_add_one hs0.ne' (H - 3 / 2)).symm
    have h2 : H - 3 / 2 + 1 = H - 1 / 2 := by ring
    rw [h2] at h1
    exact h1
  dsimp [betaKernel]
  have h_bk0 : H + ((0 : ℕ) : ℝ) - 3 / 2 = H - 3 / 2 := by push_cast; ring
  have h_bk1 : H + ((1 : ℕ) : ℝ) - 3 / 2 = H - 1 / 2 := by push_cast; ring
  rw [h_bk0, h_bk1, h_1s, ← h_s]
  push_cast
  ring

/-- Derivative of the regularized boundary term $\widetilde{B}(H, w, s)$ on $s \in (0, 1)$. -/
lemma hasDerivAt_transmuteRegBoundary {H : ℝ} (hH : 0 ≤ H) {w : ℂ} (hw : w ∈ UcDisk)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (transmuteRegBoundary H w)
      ((((H - 1 / 2 : ℝ) : ℂ) ^ 2 * transmuteKernel w s *
          block1d H (w + (Real.log s : ℂ)) -
        transmuteInnerKernel w s * transmuteInnerDiff (block1d H) w s) -
      Complex.exp ((H : ℂ) * w) *
        (((H - 1 / 2 : ℝ) : ℂ) ^ 2 * (betaKernel H 0 s : ℂ) -
          ((H * (H - 1 / 2) : ℝ) : ℂ) * (betaKernel H 1 s : ℂ))) s :=
  (hasDerivAt_transmuteBoundaryTerm hH hw hs).sub
    (hasDerivAt_transmuteBoundarySub H w hs)

@[simp]
lemma transmuteBoundaryKernel_one (w : ℂ) :
    transmuteBoundaryKernel w 1 = 0 := by
  dsimp [transmuteBoundaryKernel]
  rw [sub_self, Real.zero_rpow (by norm_num), mul_zero, Complex.ofReal_zero, zero_mul]

@[simp]
lemma transmuteRegBoundary_one (H : ℝ) (w : ℂ) :
    transmuteRegBoundary H w 1 = 0 := by
  dsimp [transmuteRegBoundary, transmuteBoundaryTerm, transmuteBoundarySub]
  rw [transmuteBoundaryKernel_one, zero_mul, sub_self, Real.zero_rpow (by norm_num),
    mul_zero, Complex.ofReal_zero, mul_zero, sub_zero]

/-- As $s \to 1^-$, the regularized boundary term $\widetilde{B}(H, w, s)$ tends to $0$. -/
lemma tendsto_transmuteRegBoundary_one {H : ℝ} (hH : 0 ≤ H) {w : ℂ} (hw : w ∈ UcDisk) :
    Tendsto (transmuteRegBoundary H w) (𝓝[<] 1) (𝓝 0) := by
  rw [← transmuteRegBoundary_one H w]
  refine ContinuousAt.tendsto ?_ |>.mono_left nhdsWithin_le_nhds
  have h_k : ContinuousAt (transmuteBoundaryKernel w) 1 := by
    have h1 : ContinuousAt (fun s : ℝ => s ^ (-1 / 2 : ℝ)) 1 :=
      continuousAt_id.rpow_const (Or.inl one_ne_zero)
    have h2 : ContinuousAt (fun s : ℝ => (1 - s) ^ (1 / 2 : ℝ)) 1 :=
      (continuousAt_const.sub continuousAt_id).rpow_const (Or.inr (by norm_num))
    have h3 : ContinuousAt
        (fun s : ℝ => (1 - (s : ℂ) * Complex.exp (2 * w)) ^ (1 / 2 : ℂ)) 1 :=
      (continuousAt_const.sub
        (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)).cpow
        continuousAt_const
        (one_sub_mul_exp_two_mul_mem_slitPlane hw ⟨zero_le_one, le_rfl⟩)
    exact (Complex.continuous_ofReal.continuousAt.comp (h1.mul h2)).mul h3
  have h_log : ContinuousAt (fun s : ℝ => w + (Real.log s : ℂ)) 1 :=
    continuousAt_const.add
      (Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log one_ne_zero))
  have hw1 : w + (Real.log (1 : ℝ) : ℂ) ∈ UcDisk := by simpa using hw
  have hb0 : ContinuousAt (fun s : ℝ => block1d H (w + (Real.log s : ℂ))) 1 :=
    ContinuousAt.comp (g := block1d H) (f := fun s : ℝ => w + (Real.log s : ℂ))
      (hasDerivAt_block1d hH hw1).continuousAt h_log
  have hb1 : ContinuousAt (fun s : ℝ => block1dDeriv1 H (w + (Real.log s : ℂ))) 1 :=
    ContinuousAt.comp (g := block1dDeriv1 H) (f := fun s : ℝ => w + (Real.log s : ℂ))
      (hasDerivAt_block1dDeriv1 hH hw1).continuousAt h_log
  have hz_ne : 1 - ((1 : ℝ) : ℂ) * Complex.exp w ≠ 0 := by
    intro h
    have h1 : (1 : ℂ) = ((1 : ℝ) : ℂ) * Complex.exp w := sub_eq_zero.mp h
    have h2 : (1 : ℝ) = ‖((1 : ℝ) : ℂ) * Complex.exp w‖ := by
      simpa using congrArg norm h1
    rw [Complex.ofReal_one, one_mul, Complex.norm_exp] at h2
    have h3 : Real.exp w.re < 1 := Real.exp_lt_one_iff.mpr (mem_UcDisk_iff.mp hw)
    linarith
  have h_rat : ContinuousAt
      (fun s : ℝ => (1 + (s : ℂ) * Complex.exp w) / (1 - (s : ℂ) * Complex.exp w)) 1 :=
    (continuousAt_const.add
      (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)).div
      (continuousAt_const.sub
        (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)) hz_ne
  have h_sub : ContinuousAt (transmuteBoundarySub H w) 1 := by
    have h1 : ContinuousAt (fun s : ℝ => s ^ (H - 1 / 2 : ℝ)) 1 :=
      continuousAt_id.rpow_const (Or.inl one_ne_zero)
    have h2 : ContinuousAt (fun s : ℝ => (1 - s) ^ (1 / 2 : ℝ)) 1 :=
      (continuousAt_const.sub continuousAt_id).rpow_const (Or.inr (by norm_num))
    exact continuousAt_const.mul
      (Complex.continuous_ofReal.continuousAt.comp (h1.mul h2))
  exact (h_k.mul ((h_rat.mul hb1).sub (continuousAt_const.mul hb0))).sub h_sub

/-- Smooth factor at $s = 0$ in the $n = 0$ part of $\widetilde{B}(H, w, s)$, which vanishes at
$s = 0$. -/
noncomputable def transmuteBoundaryZeroFactor (H : ℝ) (w : ℂ) (s : ℝ) : ℂ :=
  (1 - (s : ℂ) * Complex.exp (2 * w)) ^ (1 / 2 : ℂ) *
    ((H : ℂ) * ((1 + (s : ℂ) * Complex.exp w) / (1 - (s : ℂ) * Complex.exp w)) -
      (1 / 2 : ℂ)) -
    ((H - 1 / 2 : ℝ) : ℂ)

/-- The $n = 0$ head contribution to $\widetilde{B}(H, w, s)$. -/
noncomputable def transmuteRegBoundaryHead (H : ℝ) (w : ℂ) (s : ℝ) : ℂ :=
  ((s ^ (H - 1 / 2 : ℝ) * (1 - s) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
    Complex.exp ((H : ℂ) * w) * transmuteBoundaryZeroFactor H w s

/-- The $n \ge 1$ tail contribution to $\widetilde{B}(H, w, s)$. -/
noncomputable def transmuteRegBoundaryTail (H : ℝ) (w : ℂ) (s : ℝ) : ℂ :=
  transmuteBoundaryKernel w s *
    ((1 + (s : ℂ) * Complex.exp w) / (1 - (s : ℂ) * Complex.exp w) *
      (block1dDeriv1 H (w + (Real.log s : ℂ)) -
        (H : ℂ) * Complex.exp ((H : ℂ) * w) * ((s ^ H : ℝ) : ℂ)) -
      (1 / 2 : ℂ) *
        (block1d H (w + (Real.log s : ℂ)) -
          Complex.exp ((H : ℂ) * w) * ((s ^ H : ℝ) : ℂ)))

lemma transmuteRegBoundary_eq_head_add_tail (H : ℝ) (w : ℂ) {s : ℝ} (hs : 0 < s) :
    transmuteRegBoundary H w s =
      transmuteRegBoundaryHead H w s + transmuteRegBoundaryTail H w s := by
  dsimp [transmuteRegBoundary, transmuteBoundaryTerm, transmuteBoundarySub,
    transmuteBoundaryKernel, transmuteRegBoundaryHead, transmuteRegBoundaryTail,
    transmuteBoundaryZeroFactor]
  have hs_pow : s ^ (H - 1 / 2 : ℝ) = s ^ (-1 / 2 : ℝ) * s ^ H := by
    rw [← Real.rpow_add hs]
    congr 1
    ring
  rw [hs_pow]
  push_cast
  ring

@[simp]
lemma transmuteBoundaryZeroFactor_zero (H : ℝ) (w : ℂ) :
    transmuteBoundaryZeroFactor H w 0 = 0 := by
  dsimp [transmuteBoundaryZeroFactor]
  simp

lemma tendsto_transmuteRegBoundaryHead_zero {H : ℝ} (hH : 0 < H) {w : ℂ} (hw : w ∈ UcDisk) :
    Tendsto (transmuteRegBoundaryHead H w) (𝓝[>] 0) (𝓝 0) := by
  have h_slit0 : 1 - ((0 : ℝ) : ℂ) * Complex.exp (2 * w) ∈ Complex.slitPlane :=
    one_sub_mul_exp_two_mul_mem_slitPlane hw ⟨le_rfl, zero_le_one⟩
  have hd_in2 : HasDerivAt (fun s : ℝ => 1 - (s : ℂ) * Complex.exp (2 * w))
      (-Complex.exp (2 * w)) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.exp (2 * w))
        ((1 : ℂ) * Complex.exp (2 * w)) 0 :=
      (Complex.ofRealCLM.hasDerivAt).mul_const (Complex.exp (2 * w))
    exact ((hasDerivAt_const (0 : ℝ) (1 : ℂ)).sub h1).congr_deriv (by ring)
  have hd_cpow0 : DifferentiableAt ℝ
      (fun s : ℝ => (1 - (s : ℂ) * Complex.exp (2 * w)) ^ (1 / 2 : ℂ)) 0 :=
    (HasDerivAt.comp (h₂ := fun z : ℂ => z ^ (1 / 2 : ℂ))
      (h := fun s : ℝ => 1 - (s : ℂ) * Complex.exp (2 * w)) (0 : ℝ)
      (Complex.hasStrictDerivAt_cpow_const (c := (1 / 2 : ℂ)) h_slit0).hasDerivAt
      hd_in2).differentiableAt
  have hd_rat0 : DifferentiableAt ℝ
      (fun s : ℝ => (1 + (s : ℂ) * Complex.exp w) / (1 - (s : ℂ) * Complex.exp w)) 0 := by
    have h_lin : DifferentiableAt ℝ (fun s : ℝ => (s : ℂ) * Complex.exp w) 0 :=
      Complex.ofRealCLM.differentiableAt.mul_const (Complex.exp w)
    exact ((differentiableAt_const (1 : ℂ)).add h_lin).div
      ((differentiableAt_const (1 : ℂ)).sub h_lin) (by simp)
  have hd_zeroFactor : DifferentiableAt ℝ (transmuteBoundaryZeroFactor H w) 0 := by
    unfold transmuteBoundaryZeroFactor
    exact (hd_cpow0.mul (((differentiableAt_const (H : ℂ)).mul hd_rat0).sub
      (differentiableAt_const (1 / 2 : ℂ)))).sub (differentiableAt_const _)
  have h_slope : Tendsto
      (fun s : ℝ =>
        s⁻¹ • (transmuteBoundaryZeroFactor H w s - transmuteBoundaryZeroFactor H w 0))
      (𝓝[>] 0) (𝓝 (deriv (transmuteBoundaryZeroFactor H w) 0)) := by
    simpa only [zero_add] using
      (hasDerivAt_iff_tendsto_slope_zero.mp hd_zeroFactor.hasDerivAt).mono_left
        (nhdsWithin_mono 0 fun s (hs : s ∈ Ioi (0 : ℝ)) => ne_of_gt hs)
  have h_pre_cont : ContinuousAt
      (fun s : ℝ =>
        ((s ^ (H + 1 / 2 : ℝ) * (1 - s) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
          Complex.exp ((H : ℂ) * w)) 0 := by
    have h1 : ContinuousAt (fun s : ℝ => s ^ (H + 1 / 2 : ℝ)) 0 :=
      continuousAt_id.rpow_const (Or.inr (by linarith))
    have h2 : ContinuousAt (fun s : ℝ => (1 - s) ^ (1 / 2 : ℝ)) 0 :=
      (continuousAt_const.sub continuousAt_id).rpow_const (Or.inr (by norm_num))
    exact (Complex.continuous_ofReal.continuousAt.comp (h1.mul h2)).mul continuousAt_const
  have h_pre_tendsto : Tendsto
      (fun s : ℝ =>
        ((s ^ (H + 1 / 2 : ℝ) * (1 - s) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
          Complex.exp ((H : ℂ) * w))
      (𝓝[>] 0) (𝓝 0) := by
    have h0 : (((0 : ℝ) ^ (H + 1 / 2 : ℝ) * (1 - 0) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        Complex.exp ((H : ℂ) * w) = 0 := by
      rw [Real.zero_rpow (by linarith), zero_mul, Complex.ofReal_zero, zero_mul]
    have h_t := h_pre_cont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rwa [h0] at h_t
  have h_prod := h_pre_tendsto.mul h_slope
  rw [zero_mul] at h_prod
  refine h_prod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  rw [transmuteBoundaryZeroFactor_zero, sub_zero, Complex.real_smul]
  dsimp [transmuteRegBoundaryHead]
  have hs_pow : s ^ (H + 1 / 2 : ℝ) * s⁻¹ = s ^ (H - 1 / 2 : ℝ) := by
    rw [← div_eq_mul_inv]
    have h1 := (Real.rpow_sub_one hs.ne' (H + 1 / 2)).symm
    have h2 : H + 1 / 2 - 1 = H - 1 / 2 := by ring
    rw [h2] at h1
    exact h1
  rw [← hs_pow]
  push_cast
  ring

lemma tendsto_transmuteRegBoundaryTail_zero {H : ℝ} (hH : 0 < H) {w : ℂ} (hw : w ∈ UcDisk) :
    Tendsto (transmuteRegBoundaryTail H w) (𝓝[>] 0) (𝓝 0) := by
  have hH0 : 0 ≤ H := hH.le
  have hs0_norm : Summable (fun n : ℕ => ‖block1dTerm H (n + 1) w‖) :=
    ((summable_nat_add_iff 1).mpr (summable_block1dTerm hH0 hw)).norm
  have hs1_norm : Summable (fun n : ℕ => ‖block1dDeriv1Term H (n + 1) w‖) :=
    ((summable_nat_add_iff 1).mpr (summable_block1dDeriv1Term hH0 hw)).norm
  set C0 : ℝ := ∑' n : ℕ, ‖block1dTerm H (n + 1) w‖
  set C1 : ℝ := ∑' n : ℕ, ‖block1dDeriv1Term H (n + 1) w‖
  set C_tot : ℝ := Real.sqrt 2 * (4 * C1 + (1 / 2) * C0)
  have h_bound : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖transmuteRegBoundaryTail H w s‖ ≤ C_tot * s ^ (H + 3 / 2 : ℝ) := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with s hs
    have hs0 : 0 < s := hs.1
    have hs_ioo : s ∈ Ioo (0 : ℝ) 1 := ⟨hs.1, by linarith [hs.2]⟩
    have hs_ioc : s ∈ Ioc (0 : ℝ) (1 / 2) := ⟨hs.1, hs.2.le⟩
    set z : ℂ := w + (Real.log s : ℂ)
    have hz : z ∈ UcDisk := by
      rw [mem_UcDisk_iff]
      have hlog : Real.log s < 0 := Real.log_neg hs_ioo.1 hs_ioo.2
      have hre : z.re = w.re + Real.log s := by simp [z, Complex.add_re]
      linarith [mem_UcDisk_iff.mp hw]
    have h_term0_shift : ∀ n : ℕ,
        block1dTerm H n z = ((s ^ (H + 2 * (n : ℝ)) : ℝ) : ℂ) * block1dTerm H n w := by
      intro n
      dsimp [block1dTerm, z]
      have h_exp : Complex.exp (((H + 2 * (n : ℝ) : ℝ) : ℂ) * (w + (Real.log s : ℂ))) =
          ((s ^ (H + 2 * (n : ℝ)) : ℝ) : ℂ) *
            Complex.exp (((H + 2 * (n : ℝ) : ℝ) : ℂ) * w) := by
        rw [mul_add, Complex.exp_add, mul_comm _ (Real.log s : ℂ), ← Complex.ofReal_mul,
          ← Complex.ofReal_exp, ← Real.rpow_def_of_pos hs0, mul_comm]
      rw [h_exp]
      ring
    have h_term1_shift : ∀ n : ℕ,
        block1dDeriv1Term H n z =
          ((s ^ (H + 2 * (n : ℝ)) : ℝ) : ℂ) * block1dDeriv1Term H n w := by
      intro n
      dsimp [block1dDeriv1Term, z]
      have h_exp : Complex.exp (((H + 2 * (n : ℝ) : ℝ) : ℂ) * (w + (Real.log s : ℂ))) =
          ((s ^ (H + 2 * (n : ℝ)) : ℝ) : ℂ) *
            Complex.exp (((H + 2 * (n : ℝ) : ℝ) : ℂ) * w) := by
        rw [mul_add, Complex.exp_add, mul_comm _ (Real.log s : ℂ), ← Complex.ofReal_mul,
          ← Complex.ofReal_exp, ← Real.rpow_def_of_pos hs0, mul_comm]
      rw [h_exp]
      ring
    have h_b0_diff :
        block1d H z - Complex.exp ((H : ℂ) * w) * ((s ^ H : ℝ) : ℂ) =
          ∑' n : ℕ, block1dTerm H (n + 1) z := by
      have h_split := (summable_block1dTerm hH0 hz).tsum_eq_zero_add
      have h0 : block1dTerm H 0 z = Complex.exp ((H : ℂ) * w) * ((s ^ H : ℝ) : ℂ) := by
        rw [h_term0_shift 0]
        dsimp [block1dTerm]
        simp [mul_comm]
      change (∑' n : ℕ, block1dTerm H n z) - _ = _
      rw [h_split, h0, add_sub_cancel_left]
    have h_b1_diff :
        block1dDeriv1 H z - (H : ℂ) * Complex.exp ((H : ℂ) * w) * ((s ^ H : ℝ) : ℂ) =
          ∑' n : ℕ, block1dDeriv1Term H (n + 1) z := by
      have h_split := (summable_block1dDeriv1Term hH0 hz).tsum_eq_zero_add
      have h0 : block1dDeriv1Term H 0 z =
          (H : ℂ) * Complex.exp ((H : ℂ) * w) * ((s ^ H : ℝ) : ℂ) := by
        rw [h_term1_shift 0]
        dsimp [block1dDeriv1Term]
        simp
        ring
      change (∑' n : ℕ, block1dDeriv1Term H n z) - _ = _
      rw [h_split, h0, add_sub_cancel_left]
    have h_b0_norm :
        ‖block1d H z - Complex.exp ((H : ℂ) * w) * ((s ^ H : ℝ) : ℂ)‖ ≤
          s ^ (H + 2) * C0 := by
      rw [h_b0_diff]
      have h_sum_z : Summable (fun n : ℕ => ‖block1dTerm H (n + 1) z‖) :=
        ((summable_nat_add_iff 1).mpr (summable_block1dTerm hH0 hz)).norm
      have h_le : ∀ n : ℕ,
          ‖block1dTerm H (n + 1) z‖ ≤ s ^ (H + 2) * ‖block1dTerm H (n + 1) w‖ := by
        intro n
        rw [h_term0_shift (n + 1), norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        have h_ge : H + 2 ≤ H + 2 * ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
        exact Real.rpow_le_rpow_of_exponent_ge hs_ioo.1 hs_ioo.2.le h_ge
      calc
        ‖∑' n : ℕ, block1dTerm H (n + 1) z‖
          ≤ ∑' n : ℕ, ‖block1dTerm H (n + 1) z‖ := norm_tsum_le_tsum_norm h_sum_z
        _ ≤ ∑' n : ℕ, s ^ (H + 2) * ‖block1dTerm H (n + 1) w‖ :=
            h_sum_z.tsum_le_tsum h_le (hs0_norm.mul_left (s ^ (H + 2)))
        _ = s ^ (H + 2) * C0 := tsum_mul_left
    have h_b1_norm :
        ‖block1dDeriv1 H z - (H : ℂ) * Complex.exp ((H : ℂ) * w) * ((s ^ H : ℝ) : ℂ)‖ ≤
          s ^ (H + 2) * C1 := by
      rw [h_b1_diff]
      have h_sum_z : Summable (fun n : ℕ => ‖block1dDeriv1Term H (n + 1) z‖) :=
        ((summable_nat_add_iff 1).mpr (summable_block1dDeriv1Term hH0 hz)).norm
      have h_le : ∀ n : ℕ,
          ‖block1dDeriv1Term H (n + 1) z‖ ≤
            s ^ (H + 2) * ‖block1dDeriv1Term H (n + 1) w‖ := by
        intro n
        rw [h_term1_shift (n + 1), norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        have h_ge : H + 2 ≤ H + 2 * ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
        exact Real.rpow_le_rpow_of_exponent_ge hs_ioo.1 hs_ioo.2.le h_ge
      calc
        ‖∑' n : ℕ, block1dDeriv1Term H (n + 1) z‖
          ≤ ∑' n : ℕ, ‖block1dDeriv1Term H (n + 1) z‖ := norm_tsum_le_tsum_norm h_sum_z
        _ ≤ ∑' n : ℕ, s ^ (H + 2) * ‖block1dDeriv1Term H (n + 1) w‖ :=
            h_sum_z.tsum_le_tsum h_le (hs1_norm.mul_left (s ^ (H + 2)))
        _ = s ^ (H + 2) * C1 := tsum_mul_left
    have h_k_norm : ‖transmuteBoundaryKernel w s‖ ≤ Real.sqrt 2 * s ^ (-1 / 2 : ℝ) := by
      rw [transmuteBoundaryKernel_eq_mul_transmuteInnerKernel hw hs_ioo, norm_mul, norm_mul,
        norm_transmuteInnerKernel_eq hw hs_ioo]
      have hs1 : 0 < 1 - s := sub_pos.mpr hs_ioo.2
      have h_1s : ‖(1 - (s : ℂ))‖ = 1 - s := by
        rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_of_nonneg hs1.le]
      rw [h_1s]
      have hz_ne : 1 - (s : ℂ) * Complex.exp (2 * w) ≠ 0 :=
        Complex.slitPlane_ne_zero
          (one_sub_mul_exp_two_mul_mem_slitPlane hw ⟨hs_ioo.1.le, hs_ioo.2.le⟩)
      have hz_pos : 0 < ‖1 - (s : ℂ) * Complex.exp (2 * w)‖ := norm_pos_iff.mpr hz_ne
      have h_r1 : (1 - s) ^ (-1 / 2 : ℝ) * (1 - s) = (1 - s) ^ (1 / 2 : ℝ) := by
        have h1 := (Real.rpow_add_one hs1.ne' (-1 / 2 : ℝ)).symm
        have h2 : (-1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
        rw [h2] at h1
        exact h1
      have h_r2 :
          ‖1 - (s : ℂ) * Complex.exp (2 * w)‖ ^ (-1 / 2 : ℝ) *
            ‖1 - (s : ℂ) * Complex.exp (2 * w)‖ =
          ‖1 - (s : ℂ) * Complex.exp (2 * w)‖ ^ (1 / 2 : ℝ) := by
        have h1 := (Real.rpow_add_one hz_pos.ne' (-1 / 2 : ℝ)).symm
        have h2 : (-1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
        rw [h2] at h1
        exact h1
      have h_1s_le : (1 - s) ^ (1 / 2 : ℝ) ≤ 1 :=
        Real.rpow_le_one hs1.le (by linarith) (by norm_num)
      have h_2w_le2 : ‖1 - (s : ℂ) * Complex.exp (2 * w)‖ ≤ 2 := by
        have h1 := norm_sub_le (1 : ℂ) ((s : ℂ) * Complex.exp (2 * w))
        have h2 : ‖(s : ℂ) * Complex.exp (2 * w)‖ < 1 :=
          norm_mul_exp_two_mul_lt_one hw hs_ioo
        rw [norm_one] at h1
        linarith
      have h_2w_rpow : ‖1 - (s : ℂ) * Complex.exp (2 * w)‖ ^ (1 / 2 : ℝ) ≤ Real.sqrt 2 := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow hz_pos.le h_2w_le2 (by norm_num)
      calc
        s ^ (-1 / 2 : ℝ) * (1 - s) ^ (-1 / 2 : ℝ) *
            ‖1 - (s : ℂ) * Complex.exp (2 * w)‖ ^ (-1 / 2 : ℝ) * (1 - s) *
            ‖1 - (s : ℂ) * Complex.exp (2 * w)‖
          = s ^ (-1 / 2 : ℝ) * ((1 - s) ^ (-1 / 2 : ℝ) * (1 - s)) *
              (‖1 - (s : ℂ) * Complex.exp (2 * w)‖ ^ (-1 / 2 : ℝ) *
                ‖1 - (s : ℂ) * Complex.exp (2 * w)‖) := by ring
        _ = s ^ (-1 / 2 : ℝ) * (1 - s) ^ (1 / 2 : ℝ) *
              ‖1 - (s : ℂ) * Complex.exp (2 * w)‖ ^ (1 / 2 : ℝ) := by rw [h_r1, h_r2]
        _ ≤ s ^ (-1 / 2 : ℝ) * 1 * Real.sqrt 2 := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left h_1s_le (by positivity))
              h_2w_rpow (by positivity) (by positivity)
        _ = Real.sqrt 2 * s ^ (-1 / 2 : ℝ) := by ring
    have h_rat_le : ‖(1 + (s : ℂ) * Complex.exp w) / (1 - (s : ℂ) * Complex.exp w)‖ ≤ 4 := by
      rw [norm_div]
      have h1 := norm_one_add_mul_exp_le_two hw hs_ioc
      have h2 := half_le_norm_one_sub_mul_exp hw hs_ioc
      calc
        ‖1 + (s : ℂ) * Complex.exp w‖ / ‖1 - (s : ℂ) * Complex.exp w‖
          ≤ 2 / (1 / 2) := div_le_div₀ (by norm_num) h1 (by norm_num) h2
        _ = 4 := by norm_num
    dsimp [transmuteRegBoundaryTail]
    rw [norm_mul]
    have h_inner_le :
        ‖(1 + (s : ℂ) * Complex.exp w) / (1 - (s : ℂ) * Complex.exp w) *
            (block1dDeriv1 H z - (H : ℂ) * Complex.exp ((H : ℂ) * w) * ((s ^ H : ℝ) : ℂ)) -
          (1 / 2 : ℂ) *
            (block1d H z - Complex.exp ((H : ℂ) * w) * ((s ^ H : ℝ) : ℂ))‖ ≤
          (4 * C1 + (1 / 2) * C0) * s ^ (H + 2) := by
      have h_t1 :
          ‖(1 + (s : ℂ) * Complex.exp w) / (1 - (s : ℂ) * Complex.exp w) *
            (block1dDeriv1 H z - (H : ℂ) * Complex.exp ((H : ℂ) * w) * ((s ^ H : ℝ) : ℂ))‖ ≤
          4 * (s ^ (H + 2) * C1) := by
        rw [norm_mul]
        exact mul_le_mul h_rat_le h_b1_norm (norm_nonneg _) (by norm_num)
      have h_t2 :
          ‖(1 / 2 : ℂ) * (block1d H z - Complex.exp ((H : ℂ) * w) * ((s ^ H : ℝ) : ℂ))‖ ≤
            (1 / 2) * (s ^ (H + 2) * C0) := by
        rw [norm_mul]
        have h_half : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
        rw [h_half]
        exact mul_le_mul_of_nonneg_left h_b0_norm (by norm_num)
      calc
        ‖(1 + (s : ℂ) * Complex.exp w) / (1 - (s : ℂ) * Complex.exp w) *
            (block1dDeriv1 H z - (H : ℂ) * Complex.exp ((H : ℂ) * w) * ((s ^ H : ℝ) : ℂ)) -
          (1 / 2 : ℂ) *
            (block1d H z - Complex.exp ((H : ℂ) * w) * ((s ^ H : ℝ) : ℂ))‖
          ≤ 4 * (s ^ (H + 2) * C1) + (1 / 2) * (s ^ (H + 2) * C0) :=
            (norm_sub_le _ _).trans (add_le_add h_t1 h_t2)
        _ = (4 * C1 + (1 / 2) * C0) * s ^ (H + 2) := by ring
    have hs_rpow : s ^ (-1 / 2 : ℝ) * s ^ (H + 2) = s ^ (H + 3 / 2 : ℝ) := by
      rw [← Real.rpow_add hs0]
      congr 1
      ring
    have hC0_nonneg : 0 ≤ C0 := tsum_nonneg fun _ => norm_nonneg _
    have hC1_nonneg : 0 ≤ C1 := tsum_nonneg fun _ => norm_nonneg _
    calc
      ‖transmuteBoundaryKernel w s‖ *
          ‖(1 + (s : ℂ) * Complex.exp w) / (1 - (s : ℂ) * Complex.exp w) *
              (block1dDeriv1 H z - (H : ℂ) * Complex.exp ((H : ℂ) * w) * ((s ^ H : ℝ) : ℂ)) -
            (1 / 2 : ℂ) *
              (block1d H z - Complex.exp ((H : ℂ) * w) * ((s ^ H : ℝ) : ℂ))‖
        ≤ (Real.sqrt 2 * s ^ (-1 / 2 : ℝ)) * ((4 * C1 + (1 / 2) * C0) * s ^ (H + 2)) :=
          mul_le_mul h_k_norm h_inner_le (norm_nonneg _) (by positivity)
      _ = C_tot * (s ^ (-1 / 2 : ℝ) * s ^ (H + 2)) := by dsimp [C_tot]; ring
      _ = C_tot * s ^ (H + 3 / 2 : ℝ) := by rw [hs_rpow]
  have h_tendsto_rhs : Tendsto (fun s : ℝ => C_tot * s ^ (H + 3 / 2 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have h_cont : ContinuousAt (fun s : ℝ => C_tot * s ^ (H + 3 / 2 : ℝ)) 0 :=
      continuousAt_const.mul (continuousAt_id.rpow_const (Or.inr (by linarith)))
    have h0 : C_tot * (0 : ℝ) ^ (H + 3 / 2 : ℝ) = 0 := by
      rw [Real.zero_rpow (by linarith), mul_zero]
    have h_t := h_cont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rwa [h0] at h_t
  exact squeeze_zero_norm' h_bound h_tendsto_rhs

/-- As $s \to 0^+$, the regularized boundary term $\widetilde{B}(H, w, s)$ tends to $0$ for all
$H > 0$. -/
lemma tendsto_transmuteRegBoundary_zero {H : ℝ} (hH : 0 < H) {w : ℂ} (hw : w ∈ UcDisk) :
    Tendsto (transmuteRegBoundary H w) (𝓝[>] 0) (𝓝 0) := by
  have h_sum := (tendsto_transmuteRegBoundaryHead_zero hH hw).add
    (tendsto_transmuteRegBoundaryTail_zero hH hw)
  rw [add_zero] at h_sum
  refine h_sum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  exact (transmuteRegBoundary_eq_head_add_tail H w hs).symm

/-- Unified Pochhammer cancellation identity for `block1dCoeff` valid for all $H > 0$. -/
lemma block1dCoeff_mul_pochhammer_div_add_succ_of_pos {H : ℝ} (hH : 0 < H) (n p : ℕ) :
    block1dCoeff H n *
        (realPochhammer (H - 1 / 2) (n + 1 + p) / realPochhammer H (n + 1 + p)) =
      (H - 1 / 2) * halfBinom n *
        (realPochhammer (H + (n : ℝ) + 1 / 2) p / realPochhammer (H + (n : ℝ)) (p + 1)) := by
  have hH_half_pos : 0 < H + 1 / 2 := by linarith
  have h_num :
      realPochhammer (H - 1 / 2) (n + 1 + p) =
        (H - 1 / 2) * realPochhammer (H + 1 / 2) n *
          realPochhammer (H + (n : ℝ) + 1 / 2) p := by
    have h_idx : n + 1 + p = (n + p) + 1 := by omega
    rw [h_idx, realPochhammer_succ_left (H - 1 / 2) (n + p)]
    have h1 : H - 1 / 2 + 1 = H + 1 / 2 := by ring
    have h2 : H + 1 / 2 + (n : ℝ) = H + (n : ℝ) + 1 / 2 := by ring
    rw [h1, realPochhammer_add (H + 1 / 2) n p, h2, mul_assoc]
  have h_den :
      realPochhammer H (n + 1 + p) =
        realPochhammer H n * realPochhammer (H + (n : ℝ)) (p + 1) := by
    have h_idx : n + 1 + p = n + (p + 1) := by omega
    rw [h_idx, realPochhammer_add H n (p + 1)]
  rw [block1dCoeff_eq_halfBinom_mul_div, h_num, h_den]
  set A := realPochhammer H n
  set B := realPochhammer (H + 1 / 2) n
  set C := realPochhammer (H + (n : ℝ) + 1 / 2) p
  set D := realPochhammer (H + (n : ℝ)) (p + 1)
  have hA : A ≠ 0 := (realPochhammer_pos hH n).ne'
  have hB : B ≠ 0 := (realPochhammer_pos hH_half_pos n).ne'
  have hD : D ≠ 0 := (realPochhammer_pos (by positivity) (p + 1)).ne'
  field_simp [hA, hB, hD]

lemma block1dCoeff_mul_pochhammer_div_succ_of_pos {H : ℝ} (hH : 0 < H) (m k : ℕ) :
    block1dCoeff H k *
        (realPochhammer (H - 1 / 2) (m + 1 + k) / realPochhammer H (m + 1 + k)) =
      (H - 1 / 2) * halfBinom k *
        (realPochhammer (H + (k : ℝ) + 1 / 2) m /
          realPochhammer (H + (k : ℝ)) (m + 1)) := by
  have h_idx : m + 1 + k = k + 1 + m := by omega
  rw [h_idx, block1dCoeff_mul_pochhammer_div_add_succ_of_pos hH k m]

/-- Exact vanishing of higher descendant modes extended to all $H > 0$. -/
theorem sum_transmuteCoeff_eq_of_pos {H : ℝ} (hH : 0 < H) {m : ℕ} (hm : 1 ≤ m) :
    (∑ n ∈ Finset.range (m + 1),
      halfBinom (m - n) * block1dCoeff H n *
        (realPochhammer (H - 1 / 2) (m + n) / realPochhammer H (m + n))) =
    (∑ k ∈ Finset.range m,
      halfBinom (m - 1 - k) * block1dCoeff H k *
        (realPochhammer (H - 1 / 2) (m + 1 + k) / realPochhammer H (m + 1 + k))) := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le' hm
  simp only [Nat.add_sub_cancel]
  have h_lhs :
      (∑ n ∈ Finset.range (p + 1 + 1),
        halfBinom (p + 1 - n) * block1dCoeff H n *
          (realPochhammer (H - 1 / 2) (p + 1 + n) / realPochhammer H (p + 1 + n))) =
      ∑ n ∈ Finset.range (p + 1 + 1),
        ∑ k ∈ Finset.range (p + 1),
          (H - 1 / 2) * (halfBinom (p + 1 - n) * halfBinom n *
            halfBinom k * halfBinom (p - k) / (H + (n : ℝ) + (k : ℝ))) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_assoc (halfBinom (p + 1 - n)),
      block1dCoeff_mul_pochhammer_div_succ_of_pos hH p n,
      ← sum_halfBinom_div_add_eq_pochhammer_div p
        (fun k _ => by positivity : ∀ k ≤ p, H + (n : ℝ) + (k : ℝ) ≠ 0),
      Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have h_rhs :
      (∑ k ∈ Finset.range (p + 1),
        halfBinom (p - k) * block1dCoeff H k *
          (realPochhammer (H - 1 / 2) (p + 1 + 1 + k) / realPochhammer H (p + 1 + 1 + k))) =
      ∑ k ∈ Finset.range (p + 1),
        ∑ n ∈ Finset.range (p + 1 + 1),
          (H - 1 / 2) * (halfBinom (p + 1 - n) * halfBinom n *
            halfBinom k * halfBinom (p - k) / (H + (n : ℝ) + (k : ℝ))) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc (halfBinom (p - k)),
      block1dCoeff_mul_pochhammer_div_succ_of_pos hH (p + 1) k,
      ← sum_halfBinom_div_add_eq_pochhammer_div (p + 1)
        (fun n _ => by positivity : ∀ n ≤ p + 1, H + (k : ℝ) + (n : ℝ) ≠ 0),
      Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    have h_add : H + (k : ℝ) + (n : ℝ) = H + (n : ℝ) + (k : ℝ) := by ring
    rw [h_add]
    ring
  rw [h_lhs, h_rhs, Finset.sum_comm]

/-- Shifting the mode index by $1$ in `betaKernel` shifts $H$ by $+1$. -/
lemma betaKernel_succ (H : ℝ) (N : ℕ) (s : ℝ) :
    betaKernel H (N + 1) s = betaKernel (H + 1) N s := by
  dsimp [betaKernel]
  congr 2
  push_cast
  ring

/-- For all $H > 0$ and $N \in \mathbb{N}$, `betaKernel H (N + 1)` is integrable on $(0, 1)$. -/
lemma integrableOn_betaKernel_succ {H : ℝ} (hH : 0 < H) (N : ℕ) :
    IntegrableOn (betaKernel H (N + 1)) (Ioo (0 : ℝ) 1) volume := by
  have h_eq : betaKernel H (N + 1) = betaKernel (H + 1) N := funext (betaKernel_succ H N)
  rw [h_eq]
  exact integrableOn_betaKernel (by linarith : 1 / 2 < H + 1) N

/-- Evaluation of $(H - 1/2)^2 \int_0^1 \operatorname{betaKernel}(H, N + 1, s)\,ds$ for all
$H > 0$ and $N \in \mathbb{N}$. -/
lemma mul_sq_integral_betaKernel_succ {H : ℝ} (hH : 0 < H) (N : ℕ) :
    (H - 1 / 2) ^ 2 * (∫ s in Ioo (0 : ℝ) 1, betaKernel H (N + 1) s) =
      Real.sqrt π * transmuteWeight H *
        (realPochhammer (H - 1 / 2) (N + 1) / realPochhammer H (N + 1)) := by
  simp_rw [betaKernel_succ]
  rw [integral_betaKernel (by linarith : 1 / 2 < H + 1) N]
  dsimp [transmuteCoreWeight, transmuteWeight]
  have h_g1 : H + 1 - 1 / 2 = H + 1 / 2 := by ring
  rw [h_g1, Real.Gamma_add_one hH.ne',
    realPochhammer_succ_left (H - 1 / 2) N,
    realPochhammer_succ_left H N]
  have h_p1 : H - 1 / 2 + 1 = H + 1 / 2 := by ring
  rw [h_p1]
  have hG_ne : Real.Gamma H ≠ 0 := (Real.Gamma_pos_of_pos hH).ne'
  have hP_ne : realPochhammer (H + 1) N ≠ 0 := (realPochhammer_pos (by linarith) N).ne'
  field_simp [hH.ne', hG_ne, hP_ne]

/-- Evaluation of $H(H - 1/2) \int_0^1 \operatorname{betaKernel}(H, 1, s)\,ds$ for all $H > 0$. -/
lemma mul_integral_betaKernel_one {H : ℝ} (hH : 0 < H) :
    H * (H - 1 / 2) * (∫ s in Ioo (0 : ℝ) 1, betaKernel H 1 s) =
      Real.sqrt π * transmuteWeight H := by
  simp_rw [betaKernel_succ H 0]
  rw [integral_betaKernel (by linarith : 1 / 2 < H + 1) 0]
  simp only [realPochhammer_zero, div_one, mul_one]
  dsimp [transmuteCoreWeight, transmuteWeight]
  have h_g1 : H + 1 - 1 / 2 = H + 1 / 2 := by ring
  rw [h_g1, Real.Gamma_add_one hH.ne']
  have hG_ne : Real.Gamma H ≠ 0 := (Real.Gamma_pos_of_pos hH).ne'
  field_simp [hH.ne', hG_ne]

/-- Linear growth bound on `|transmuteModeSum H m|` valid for all $H > 0$. -/
lemma abs_transmuteModeSum_le_of_pos {H : ℝ} (hH : 0 < H) (m : ℕ) :
    |transmuteModeSum H m| ≤ (1 + |H - 1 / 2| / H) * ((m : ℝ) + 1) := by
  have h_ratio_nonneg : 0 ≤ |H - 1 / 2| / H := div_nonneg (abs_nonneg _) hH.le
  rcases m with _ | k
  · simp only [transmuteModeSum_zero, abs_one, Nat.cast_zero, zero_add, mul_one]
    linarith
  · dsimp [transmuteModeSum]
    calc
      |∑ n ∈ Finset.range (k + 1 + 1),
          halfBinom (k + 1 - n) * block1dCoeff H n *
            (realPochhammer (H - 1 / 2) (k + 1 + n) / realPochhammer H (k + 1 + n))|
        ≤ ∑ n ∈ Finset.range (k + 1 + 1),
            |halfBinom (k + 1 - n) * block1dCoeff H n *
              (realPochhammer (H - 1 / 2) (k + 1 + n) / realPochhammer H (k + 1 + n))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ Finset.range (k + 1 + 1), (1 + |H - 1 / 2| / H) := by
          refine Finset.sum_le_sum fun n _ => ?_
          have h_idx : k + 1 + n = (k + n) + 1 := by omega
          rw [h_idx, realPochhammer_succ_left (H - 1 / 2) (k + n),
            realPochhammer_succ_left H (k + n)]
          have h_p1 : H - 1 / 2 + 1 = H + 1 / 2 := by ring
          rw [h_p1]
          have h1 : 0 ≤ halfBinom (k + 1 - n) * block1dCoeff H n :=
            mul_nonneg (halfBinom_nonneg _) (block1dCoeff_nonneg hH.le n)
          have h1_le : halfBinom (k + 1 - n) * block1dCoeff H n ≤ 1 :=
            (mul_le_of_le_one_left (block1dCoeff_nonneg hH.le n)
              (halfBinom_le_one _)).trans (block1dCoeff_le_one hH.le n)
          have h_poch_ratio_nonneg :
              0 ≤ realPochhammer (H + 1 / 2) (k + n) / realPochhammer (H + 1) (k + n) :=
            div_nonneg (realPochhammer_nonneg (by linarith) _)
              (realPochhammer_pos (by linarith) _).le
          have h_poch_ratio_le :
              realPochhammer (H + 1 / 2) (k + n) / realPochhammer (H + 1) (k + n) ≤ 1 := by
            rw [div_le_one (realPochhammer_pos (by linarith) _)]
            exact realPochhammer_mono (by linarith) (by linarith) (k + n)
          have h_split :
              (H - 1 / 2) * realPochhammer (H + 1 / 2) (k + n) /
                (H * realPochhammer (H + 1) (k + n)) =
              ((H - 1 / 2) / H) *
                (realPochhammer (H + 1 / 2) (k + n) / realPochhammer (H + 1) (k + n)) := by
            ring
          have h_abs_eq :
              |halfBinom (k + 1 - n) * block1dCoeff H n *
                ((H - 1 / 2) * realPochhammer (H + 1 / 2) (k + n) /
                  (H * realPochhammer (H + 1) (k + n)))| =
              halfBinom (k + 1 - n) * block1dCoeff H n *
                (|H - 1 / 2| / H *
                  (realPochhammer (H + 1 / 2) (k + n) / realPochhammer (H + 1) (k + n))) := by
            rw [h_split, abs_mul, abs_of_nonneg h1, abs_mul, abs_div, abs_of_pos hH,
              abs_of_nonneg h_poch_ratio_nonneg]
          rw [h_abs_eq]
          have h_prod_le :
              halfBinom (k + 1 - n) * block1dCoeff H n *
                (|H - 1 / 2| / H *
                  (realPochhammer (H + 1 / 2) (k + n) / realPochhammer (H + 1) (k + n))) ≤
              1 * (|H - 1 / 2| / H * 1) :=
            mul_le_mul h1_le
              (mul_le_mul_of_nonneg_left h_poch_ratio_le h_ratio_nonneg)
              (by positivity) zero_le_one
          linarith
      _ = (1 + |H - 1 / 2| / H) * (((k + 1 : ℕ) : ℝ) + 1) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
          ring

/-- Pointwise series expansion of `transmuteKernel w s * block1d H (w + Real.log s)` valid for all
$H \ge 0$. -/
lemma hasSum_transmuteModeTerm_of_nonneg {H : ℝ} (hH : 0 ≤ H) {w : ℂ} (hw : w ∈ UcDisk)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun m : ℕ => transmuteModeTerm H w m s)
      (transmuteKernel w s * block1d H (w + (Real.log s : ℂ))) := by
  have hs0 : 0 < s := hs.1
  set q : ℂ := Complex.exp (2 * w)
  have hq_norm : ‖q‖ = Real.exp (2 * w.re) := by
    dsimp [q]; rw [Complex.norm_exp]; simp [Complex.mul_re]
  have hq_lt1 : Real.exp (2 * w.re) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith [mem_UcDisk_iff.mp hw])
  set f : ℕ → ℂ := fun n =>
    ((block1dCoeff H n * s ^ (H + 2 * (n : ℝ)) : ℝ) : ℂ) * q ^ n
  set g : ℕ → ℂ := fun k =>
    ((halfBinom k * s ^ k : ℝ) : ℂ) * q ^ k
  have hf_norm : Summable (fun n : ℕ => ‖f n‖) := by
    have h_geom : Summable (fun n : ℕ => s ^ H * (Real.exp (2 * w.re)) ^ n) :=
      (summable_geometric_of_lt_one (by positivity) hq_lt1).mul_left (s ^ H)
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) h_geom
    dsimp [f]
    rw [norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (mul_nonneg (block1dCoeff_nonneg hH n) (by positivity)),
      norm_pow, hq_norm]
    have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hs_le : s ^ (H + 2 * (n : ℝ)) ≤ s ^ H :=
      Real.rpow_le_rpow_of_exponent_ge hs.1 hs.2.le (by linarith)
    have hc_le : block1dCoeff H n * s ^ (H + 2 * (n : ℝ)) ≤ s ^ H := by
      calc
        block1dCoeff H n * s ^ (H + 2 * (n : ℝ))
          ≤ 1 * s ^ H :=
            mul_le_mul (block1dCoeff_le_one hH n) hs_le (by positivity) zero_le_one
        _ = s ^ H := one_mul _
    exact mul_le_mul_of_nonneg_right hc_le (by positivity)
  have hg_norm : Summable (fun k : ℕ => ‖g k‖) := by
    have h_geom : Summable (fun k : ℕ => (Real.exp (2 * w.re)) ^ k) :=
      summable_geometric_of_lt_one (by positivity) hq_lt1
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) h_geom
    dsimp [g]
    rw [norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (mul_nonneg (halfBinom_nonneg k) (pow_nonneg hs.1.le k)),
      norm_pow, hq_norm]
    have hs_le : s ^ k ≤ 1 := pow_le_one₀ hs.1.le hs.2.le
    have hb_le : halfBinom k * s ^ k ≤ 1 :=
      (mul_le_of_le_one_left (pow_nonneg hs.1.le k) (halfBinom_le_one k)).trans hs_le
    calc
      halfBinom k * s ^ k * (Real.exp (2 * w.re)) ^ k
        ≤ 1 * (Real.exp (2 * w.re)) ^ k :=
          mul_le_mul_of_nonneg_right hb_le (by positivity)
      _ = (Real.exp (2 * w.re)) ^ k := one_mul _
  have hf_sum : Complex.exp ((H : ℂ) * w) * (∑' n : ℕ, f n) =
      block1d H (w + (Real.log s : ℂ)) := by
    dsimp [block1d]
    rw [← tsum_mul_left]
    congr 1 with n
    dsimp [f, q]
    have h_exp_log :
        Complex.exp (((H + 2 * (n : ℝ) : ℝ) : ℂ) * (Real.log s : ℂ)) =
          ((s ^ (H + 2 * (n : ℝ)) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, mul_comm, ← Real.rpow_def_of_pos hs.1]
    have h_exp_w :
        Complex.exp (((H + 2 * (n : ℝ) : ℝ) : ℂ) * (w + (Real.log s : ℂ))) =
          Complex.exp ((H : ℂ) * w) * (Complex.exp (2 * w)) ^ n *
            ((s ^ (H + 2 * (n : ℝ)) : ℝ) : ℂ) := by
      rw [mul_add, Complex.exp_add, h_exp_log, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    rw [h_exp_w]
    push_cast
    ring
  have hg_sum : (∑' k : ℕ, g k) = (1 - (s : ℂ) * Complex.exp (2 * w)) ^ (-1 / 2 : ℂ) := by
    have h_bin := hasSum_one_sub_cpow_neg (1 / 2) (norm_mul_exp_two_mul_lt_one hw hs)
    have h_exp_neg : (- ((1 / 2 : ℝ) : ℂ)) = (-1 / 2 : ℂ) := by push_cast; ring
    rw [h_exp_neg] at h_bin
    have h_congr : HasSum g ((1 - (s : ℂ) * Complex.exp (2 * w)) ^ (-1 / 2 : ℂ)) := by
      refine h_bin.congr_fun fun k => ?_
      dsimp [g, q]
      rw [← halfBinom_eq_pochhammerCoeff k, mul_pow]
      push_cast
      ring
    exact h_congr.tsum_eq
  have h_cauchy := hasSum_sum_range_mul_of_summable_norm hf_norm hg_norm
  rw [hg_sum] at h_cauchy
  have h_mul := h_cauchy.mul_left
    (((s ^ (-3 / 2 : ℝ) * (1 - s) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
      (1 - ((s ^ 2 : ℝ) : ℂ) * Complex.exp (2 * w)) *
      Complex.exp ((H : ℂ) * w))
  have h_rhs_eq :
      (((s ^ (-3 / 2 : ℝ) * (1 - s) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
        (1 - ((s ^ 2 : ℝ) : ℂ) * Complex.exp (2 * w)) *
        Complex.exp ((H : ℂ) * w)) *
        ((∑' n : ℕ, f n) * (1 - (s : ℂ) * Complex.exp (2 * w)) ^ (-1 / 2 : ℂ)) =
      transmuteKernel w s * block1d H (w + (Real.log s : ℂ)) := by
    calc
      (((s ^ (-3 / 2 : ℝ) * (1 - s) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
        (1 - ((s ^ 2 : ℝ) : ℂ) * Complex.exp (2 * w)) *
        Complex.exp ((H : ℂ) * w)) *
        ((∑' n : ℕ, f n) * (1 - (s : ℂ) * Complex.exp (2 * w)) ^ (-1 / 2 : ℂ))
        = transmuteKernel w s * (Complex.exp ((H : ℂ) * w) * ∑' n : ℕ, f n) := by
          dsimp [transmuteKernel]
          ring
      _ = transmuteKernel w s * block1d H (w + (Real.log s : ℂ)) := by rw [hf_sum]
  rw [h_rhs_eq] at h_mul
  refine h_mul.congr_fun fun m => ?_
  dsimp [transmuteModeTerm]
  have h_pre :
      (((s ^ (-3 / 2 : ℝ) * (1 - s) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
        (1 - ((s ^ 2 : ℝ) : ℂ) * Complex.exp (2 * w)) *
        Complex.exp ((H : ℂ) * w)) *
        (∑ n ∈ Finset.range (m + 1), f n * g (m - n)) =
      Complex.exp ((H : ℂ) * w) *
        ∑ n ∈ Finset.range (m + 1),
          (((s ^ (-3 / 2 : ℝ) * (1 - s) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
            (1 - ((s ^ 2 : ℝ) : ℂ) * q) * (f n * g (m - n))) := by
    rw [← Finset.mul_sum]
    dsimp [q]
    ring
  rw [h_pre]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn_le : n ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  dsimp [f, g, betaKernel]
  symm
  change _ = ((halfBinom (m - n) * block1dCoeff H n : ℝ) : ℂ) *
    (((s ^ (H + ((m + n : ℕ) : ℝ) - 3 / 2) * (1 - s) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) * q ^ m -
      ((s ^ (H + ((m + 2 + n : ℕ) : ℝ) - 3 / 2) * (1 - s) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
        q ^ (m + 1))
  have hq_pow1 : q ^ n * q ^ (m - n) = q ^ m := by
    rw [← pow_add, Nat.add_sub_of_le hn_le]
  have hq_pow2 : q * q ^ m = q ^ (m + 1) := by
    rw [pow_succ']
  have hs_pow1 :
      s ^ (-3 / 2 : ℝ) * s ^ (H + 2 * (n : ℝ)) * s ^ (m - n) =
        s ^ (H + ((m + n : ℕ) : ℝ) - 3 / 2) := by
    rw [← Real.rpow_natCast s (m - n), ← Real.rpow_add hs.1, ← Real.rpow_add hs.1]
    congr 1
    rw [Nat.cast_sub hn_le, Nat.cast_add]
    ring
  have hs_pow2 :
      s ^ (-3 / 2 : ℝ) * s ^ 2 * s ^ (H + 2 * (n : ℝ)) * s ^ (m - n) =
        s ^ (H + ((m + 2 + n : ℕ) : ℝ) - 3 / 2) := by
    rw [← Real.rpow_natCast s 2, ← Real.rpow_natCast s (m - n),
      ← Real.rpow_add hs.1, ← Real.rpow_add hs.1, ← Real.rpow_add hs.1]
    congr 1
    rw [Nat.cast_sub hn_le]
    push_cast
    ring
  have h_real1 :
      ((s ^ (-3 / 2 : ℝ) * (1 - s) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
        ((block1dCoeff H n * s ^ (H + 2 * (n : ℝ)) : ℝ) : ℂ) *
        ((halfBinom (m - n) * s ^ (m - n) : ℝ) : ℂ) =
      ((halfBinom (m - n) * block1dCoeff H n : ℝ) : ℂ) *
        ((s ^ (H + ((m + n : ℕ) : ℝ) - 3 / 2) * (1 - s) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [← hs_pow1]
    push_cast
    ring
  have h_real2 :
      ((s ^ (-3 / 2 : ℝ) * (1 - s) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) * ((s ^ 2 : ℝ) : ℂ) *
        ((block1dCoeff H n * s ^ (H + 2 * (n : ℝ)) : ℝ) : ℂ) *
        ((halfBinom (m - n) * s ^ (m - n) : ℝ) : ℂ) =
      ((halfBinom (m - n) * block1dCoeff H n : ℝ) : ℂ) *
        ((s ^ (H + ((m + 2 + n : ℕ) : ℝ) - 3 / 2) * (1 - s) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [← hs_pow2]
    push_cast
    ring
  calc
    ((s ^ (-3 / 2 : ℝ) * (1 - s) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
        (1 - ((s ^ 2 : ℝ) : ℂ) * q) *
        (((block1dCoeff H n * s ^ (H + 2 * (n : ℝ)) : ℝ) : ℂ) * q ^ n *
          (((halfBinom (m - n) * s ^ (m - n) : ℝ) : ℂ) * q ^ (m - n)))
      = (((s ^ (-3 / 2 : ℝ) * (1 - s) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
          ((block1dCoeff H n * s ^ (H + 2 * (n : ℝ)) : ℝ) : ℂ) *
          ((halfBinom (m - n) * s ^ (m - n) : ℝ) : ℂ)) * (q ^ n * q ^ (m - n)) -
        (((s ^ (-3 / 2 : ℝ) * (1 - s) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) * ((s ^ 2 : ℝ) : ℂ) *
          ((block1dCoeff H n * s ^ (H + 2 * (n : ℝ)) : ℝ) : ℂ) *
          ((halfBinom (m - n) * s ^ (m - n) : ℝ) : ℂ)) *
          (q * (q ^ n * q ^ (m - n))) := by ring
    _ = ((halfBinom (m - n) * block1dCoeff H n : ℝ) : ℂ) *
          (((s ^ (H + ((m + n : ℕ) : ℝ) - 3 / 2) *
              (1 - s) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) * q ^ m -
            ((s ^ (H + ((m + 2 + n : ℕ) : ℝ) - 3 / 2) *
              (1 - s) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) * q ^ (m + 1)) := by
      rw [hq_pow1, hq_pow2, h_real1, h_real2]
      ring

/-- The regularized $m$-th mode integrand obtained by subtracting $\frac{d}{ds} S_0(H, w, s)$ from
the $m = 0$ mode of $(H - 1/2)^2 \operatorname{transmuteModeTerm}(H, w, m, s)$. -/
noncomputable def regTransmuteModeTerm (H : ℝ) (w : ℂ) (m : ℕ) (s : ℝ) : ℂ :=
  if m = 0 then
    Complex.exp ((H : ℂ) * w) *
      (((H * (H - 1 / 2) : ℝ) : ℂ) * (betaKernel H 1 s : ℂ) -
        ((H - 1 / 2 : ℝ) : ℂ) ^ 2 * (betaKernel H 2 s : ℂ) * Complex.exp (2 * w))
  else
    ((H - 1 / 2 : ℝ) : ℂ) ^ 2 * transmuteModeTerm H w m s

lemma continuousOn_regTransmuteModeTerm (H : ℝ) (w : ℂ) (m : ℕ) :
    ContinuousOn (regTransmuteModeTerm H w m) (Ioo (0 : ℝ) 1) := by
  unfold regTransmuteModeTerm
  split_ifs
  · refine continuousOn_const.mul (ContinuousOn.sub ?_ ?_)
    · exact continuousOn_const.mul
        (Complex.continuous_ofReal.comp_continuousOn (continuousOn_betaKernel H 1))
    · exact (continuousOn_const.mul
        (Complex.continuous_ofReal.comp_continuousOn (continuousOn_betaKernel H 2))).mul
        continuousOn_const
  · exact continuousOn_const.mul (continuousOn_transmuteModeTerm H w m)

lemma betaKernel_le_one (H : ℝ) {N : ℕ} (hN : 1 ≤ N) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    betaKernel H N s ≤ betaKernel H 1 s := by
  dsimp [betaKernel]
  have hs1 : 0 < 1 - s := sub_pos.mpr hs.2
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have h_ge : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN
  exact Real.rpow_le_rpow_of_exponent_ge hs.1 hs.2.le (by linarith)

lemma norm_regTransmuteModeTerm_le {H : ℝ} (hH : 0 < H) {w : ℂ} (hw : w ∈ UcDisk)
    (m : ℕ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    ‖regTransmuteModeTerm H w m s‖ ≤
      (2 * (H + 1 / 2) ^ 2 * ((m : ℝ) + 1) *
        Real.exp (H * w.re) * (Real.exp (2 * w.re)) ^ m) *
        betaKernel H 1 s := by
  have h_re_H : ((H : ℂ) * w).re = H * w.re := by simp [Complex.mul_re]
  have h_norm_q : ‖Complex.exp (2 * w)‖ = Real.exp (2 * w.re) := by
    rw [Complex.norm_exp]; simp [Complex.mul_re]
  have hq_le1 : Real.exp (2 * w.re) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith [mem_UcDisk_iff.mp hw])
  have h_bk1_nonneg : 0 ≤ betaKernel H 1 s := betaKernel_nonneg H 1 hs
  have h_sq_le : (H - 1 / 2) ^ 2 ≤ (H + 1 / 2) ^ 2 := by nlinarith
  rcases eq_or_ne m 0 with rfl | hm
  · dsimp [regTransmuteModeTerm]
    simp only [Nat.cast_zero, zero_add, mul_one, pow_zero]
    rw [norm_mul, Complex.norm_exp, h_re_H]
    have h_abs1 : |H * (H - 1 / 2)| ≤ (H + 1 / 2) ^ 2 := by
      rw [abs_le]
      constructor <;> nlinarith
    have h_t1 :
        ‖((H * (H - 1 / 2) : ℝ) : ℂ) * (betaKernel H 1 s : ℂ)‖ ≤
          (H + 1 / 2) ^ 2 * betaKernel H 1 s := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real,
        Real.norm_of_nonneg h_bk1_nonneg]
      exact mul_le_mul_of_nonneg_right h_abs1 h_bk1_nonneg
    have h_t2 :
        ‖((H - 1 / 2 : ℝ) : ℂ) ^ 2 * (betaKernel H 2 s : ℂ) * Complex.exp (2 * w)‖ ≤
          (H + 1 / 2) ^ 2 * betaKernel H 1 s := by
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
        Complex.norm_real, Real.norm_of_nonneg (betaKernel_nonneg H 2 hs), h_norm_q]
      have h_bk2 : betaKernel H 2 s ≤ betaKernel H 1 s := betaKernel_le_one H (by omega) hs
      have h_prod1 : (H - 1 / 2) ^ 2 * betaKernel H 2 s ≤
          (H + 1 / 2) ^ 2 * betaKernel H 1 s :=
        mul_le_mul h_sq_le h_bk2 (betaKernel_nonneg H 2 hs) (by positivity)
      calc
        (H - 1 / 2) ^ 2 * betaKernel H 2 s * Real.exp (2 * w.re)
          ≤ ((H + 1 / 2) ^ 2 * betaKernel H 1 s) * 1 :=
            mul_le_mul h_prod1 hq_le1 (by positivity) (by positivity)
        _ = (H + 1 / 2) ^ 2 * betaKernel H 1 s := mul_one _
    have h_diff :
        ‖((H * (H - 1 / 2) : ℝ) : ℂ) * (betaKernel H 1 s : ℂ) -
          ((H - 1 / 2 : ℝ) : ℂ) ^ 2 * (betaKernel H 2 s : ℂ) * Complex.exp (2 * w)‖ ≤
          2 * (H + 1 / 2) ^ 2 * betaKernel H 1 s := by
      calc
        ‖((H * (H - 1 / 2) : ℝ) : ℂ) * (betaKernel H 1 s : ℂ) -
          ((H - 1 / 2 : ℝ) : ℂ) ^ 2 * (betaKernel H 2 s : ℂ) * Complex.exp (2 * w)‖
          ≤ (H + 1 / 2) ^ 2 * betaKernel H 1 s + (H + 1 / 2) ^ 2 * betaKernel H 1 s :=
            (norm_sub_le _ _).trans (add_le_add h_t1 h_t2)
        _ = 2 * (H + 1 / 2) ^ 2 * betaKernel H 1 s := by ring
    calc
      Real.exp (H * w.re) *
          ‖((H * (H - 1 / 2) : ℝ) : ℂ) * (betaKernel H 1 s : ℂ) -
            ((H - 1 / 2 : ℝ) : ℂ) ^ 2 * (betaKernel H 2 s : ℂ) * Complex.exp (2 * w)‖
        ≤ Real.exp (H * w.re) * (2 * (H + 1 / 2) ^ 2 * betaKernel H 1 s) :=
          mul_le_mul_of_nonneg_left h_diff (by positivity)
      _ = 2 * (H + 1 / 2) ^ 2 * Real.exp (H * w.re) * betaKernel H 1 s := by ring
  · have hm_pos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    dsimp [regTransmuteModeTerm, transmuteModeTerm]
    simp only [hm, ↓reduceIte]
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Complex.norm_exp, h_re_H]
    have h_sum_le :
        ‖∑ n ∈ Finset.range (m + 1),
          ((halfBinom (m - n) * block1dCoeff H n : ℝ) : ℂ) *
            ((betaKernel H (m + n) s : ℂ) * (Complex.exp (2 * w)) ^ m -
              (betaKernel H (m + 2 + n) s : ℂ) * (Complex.exp (2 * w)) ^ (m + 1))‖ ≤
          ((m : ℝ) + 1) * (2 * (Real.exp (2 * w.re)) ^ m * betaKernel H 1 s) := by
      calc
        ‖∑ n ∈ Finset.range (m + 1),
          ((halfBinom (m - n) * block1dCoeff H n : ℝ) : ℂ) *
            ((betaKernel H (m + n) s : ℂ) * (Complex.exp (2 * w)) ^ m -
              (betaKernel H (m + 2 + n) s : ℂ) * (Complex.exp (2 * w)) ^ (m + 1))‖
          ≤ ∑ n ∈ Finset.range (m + 1),
              ‖((halfBinom (m - n) * block1dCoeff H n : ℝ) : ℂ) *
                ((betaKernel H (m + n) s : ℂ) * (Complex.exp (2 * w)) ^ m -
                  (betaKernel H (m + 2 + n) s : ℂ) * (Complex.exp (2 * w)) ^ (m + 1))‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _n ∈ Finset.range (m + 1),
              (2 * (Real.exp (2 * w.re)) ^ m * betaKernel H 1 s) := by
            refine Finset.sum_le_sum fun n _ => ?_
            rw [norm_mul, Complex.norm_real,
              Real.norm_of_nonneg
                (mul_nonneg (halfBinom_nonneg _) (block1dCoeff_nonneg hH.le n))]
            have h_coeff : halfBinom (m - n) * block1dCoeff H n ≤ 1 :=
              (mul_le_of_le_one_left (block1dCoeff_nonneg hH.le n)
                (halfBinom_le_one (m - n))).trans (block1dCoeff_le_one hH.le n)
            have h_term1 :
                ‖(betaKernel H (m + n) s : ℂ) * (Complex.exp (2 * w)) ^ m‖ ≤
                  betaKernel H 1 s * (Real.exp (2 * w.re)) ^ m := by
              rw [norm_mul, Complex.norm_real,
                Real.norm_of_nonneg (betaKernel_nonneg H (m + n) hs),
                norm_pow, h_norm_q]
              exact mul_le_mul_of_nonneg_right
                (betaKernel_le_one H (by omega) hs) (by positivity)
            have h_term2 :
                ‖(betaKernel H (m + 2 + n) s : ℂ) * (Complex.exp (2 * w)) ^ (m + 1)‖ ≤
                  betaKernel H 1 s * (Real.exp (2 * w.re)) ^ m := by
              rw [norm_mul, Complex.norm_real,
                Real.norm_of_nonneg (betaKernel_nonneg H (m + 2 + n) hs),
                norm_pow, h_norm_q, pow_succ]
              have h_pow_le : (Real.exp (2 * w.re)) ^ m * Real.exp (2 * w.re) ≤
                  (Real.exp (2 * w.re)) ^ m * 1 :=
                mul_le_mul_of_nonneg_left hq_le1 (by positivity)
              rw [mul_one] at h_pow_le
              exact mul_le_mul (betaKernel_le_one H (by omega) hs) h_pow_le
                (by positivity) h_bk1_nonneg
            have h_diff :
                ‖(betaKernel H (m + n) s : ℂ) * (Complex.exp (2 * w)) ^ m -
                  (betaKernel H (m + 2 + n) s : ℂ) * (Complex.exp (2 * w)) ^ (m + 1)‖ ≤
                  2 * (Real.exp (2 * w.re)) ^ m * betaKernel H 1 s := by
              calc
                ‖(betaKernel H (m + n) s : ℂ) * (Complex.exp (2 * w)) ^ m -
                  (betaKernel H (m + 2 + n) s : ℂ) * (Complex.exp (2 * w)) ^ (m + 1)‖
                  ≤ betaKernel H 1 s * (Real.exp (2 * w.re)) ^ m +
                      betaKernel H 1 s * (Real.exp (2 * w.re)) ^ m :=
                    (norm_sub_le _ _).trans (add_le_add h_term1 h_term2)
                _ = 2 * (Real.exp (2 * w.re)) ^ m * betaKernel H 1 s := by ring
            calc
              halfBinom (m - n) * block1dCoeff H n *
                  ‖(betaKernel H (m + n) s : ℂ) * (Complex.exp (2 * w)) ^ m -
                    (betaKernel H (m + 2 + n) s : ℂ) * (Complex.exp (2 * w)) ^ (m + 1)‖
                ≤ 1 * (2 * (Real.exp (2 * w.re)) ^ m * betaKernel H 1 s) :=
                  mul_le_mul h_coeff h_diff (norm_nonneg _) zero_le_one
              _ = 2 * (Real.exp (2 * w.re)) ^ m * betaKernel H 1 s := one_mul _
        _ = ((m : ℝ) + 1) * (2 * (Real.exp (2 * w.re)) ^ m * betaKernel H 1 s) := by simp
    calc
      (H - 1 / 2) ^ 2 *
          (Real.exp (H * w.re) *
            ‖∑ n ∈ Finset.range (m + 1),
              ((halfBinom (m - n) * block1dCoeff H n : ℝ) : ℂ) *
                ((betaKernel H (m + n) s : ℂ) * (Complex.exp (2 * w)) ^ m -
                   (betaKernel H (m + 2 + n) s : ℂ) * (Complex.exp (2 * w)) ^ (m + 1))‖)
        ≤ (H + 1 / 2) ^ 2 *
            (Real.exp (H * w.re) *
              (((m : ℝ) + 1) * (2 * (Real.exp (2 * w.re)) ^ m * betaKernel H 1 s))) :=
          mul_le_mul h_sq_le
            (mul_le_mul_of_nonneg_left h_sum_le (by positivity))
            (by positivity) (by positivity)
      _ = (2 * (H + 1 / 2) ^ 2 * ((m : ℝ) + 1) *
            Real.exp (H * w.re) * (Real.exp (2 * w.re)) ^ m) *
            betaKernel H 1 s := by ring

lemma hasSum_regTransmuteModeTerm {H : ℝ} (hH : 0 ≤ H) {w : ℂ} (hw : w ∈ UcDisk)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun m : ℕ => regTransmuteModeTerm H w m s)
      (((H - 1 / 2 : ℝ) : ℂ) ^ 2 *
          (transmuteKernel w s * block1d H (w + (Real.log s : ℂ))) -
        Complex.exp ((H : ℂ) * w) *
          (((H - 1 / 2 : ℝ) : ℂ) ^ 2 * (betaKernel H 0 s : ℂ) -
            ((H * (H - 1 / 2) : ℝ) : ℂ) * (betaKernel H 1 s : ℂ))) := by
  have h_base := (hasSum_transmuteModeTerm_of_nonneg hH hw hs).mul_left
    (((H - 1 / 2 : ℝ) : ℂ) ^ 2)
  have h_sub0 : HasSum
      (fun m : ℕ =>
        if m = 0 then
          Complex.exp ((H : ℂ) * w) *
            (((H - 1 / 2 : ℝ) : ℂ) ^ 2 * (betaKernel H 0 s : ℂ) -
              ((H * (H - 1 / 2) : ℝ) : ℂ) * (betaKernel H 1 s : ℂ))
        else 0)
      (Complex.exp ((H : ℂ) * w) *
        (((H - 1 / 2 : ℝ) : ℂ) ^ 2 * (betaKernel H 0 s : ℂ) -
          ((H * (H - 1 / 2) : ℝ) : ℂ) * (betaKernel H 1 s : ℂ))) :=
    hasSum_ite_eq 0 _
  refine (h_base.sub h_sub0).congr_fun fun m => ?_
  dsimp [regTransmuteModeTerm]
  split_ifs with hm
  · subst hm
    dsimp [transmuteModeTerm]
    simp only [Finset.sum_singleton, Nat.sub_zero, halfBinom_zero,
      block1dCoeff_zero, mul_one, Complex.ofReal_one, one_mul, Nat.add_zero, pow_zero, pow_one]
    ring
  · rw [sub_zero]

/-- Beta-integral evaluation of the regularized $m$-th mode `regTransmuteModeTerm H w m` for all
$H > 0$ and $m \in \mathbb{N}$. -/
lemma inv_sqrt_pi_mul_integral_regTransmuteModeTerm {H : ℝ} (hH : 0 < H) (w : ℂ) (m : ℕ) :
    ((Real.sqrt π : ℝ) : ℂ)⁻¹ * (∫ s in Ioo (0 : ℝ) 1, regTransmuteModeTerm H w m s) =
      (transmuteWeight H : ℂ) * Complex.exp ((H : ℂ) * w) *
        ((transmuteModeSum H m : ℂ) * (Complex.exp (2 * w)) ^ m -
          (transmuteModeSum H (m + 1) : ℂ) * (Complex.exp (2 * w)) ^ (m + 1)) := by
  have h_sqrt_ne : ((Real.sqrt π : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  rcases eq_or_ne m 0 with rfl | hm
  · dsimp [regTransmuteModeTerm]
    simp only [pow_zero, pow_one]
    have h1 : IntegrableOn
        (fun s : ℝ => ((H * (H - 1 / 2) : ℝ) : ℂ) * (betaKernel H 1 s : ℂ))
        (Ioo (0 : ℝ) 1) volume :=
      (integrableOn_betaKernel_succ hH 0).ofReal.const_mul _
    have h2 : IntegrableOn
        (fun s : ℝ =>
          ((H - 1 / 2 : ℝ) : ℂ) ^ 2 * (betaKernel H 2 s : ℂ) * Complex.exp (2 * w))
        (Ioo (0 : ℝ) 1) volume :=
      ((integrableOn_betaKernel_succ hH 1).ofReal.const_mul _).mul_const _
    rw [integral_const_mul, integral_sub h1 h2, integral_const_mul,
      integral_mul_const, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal]
    have hi1 := congrArg (fun r : ℝ => (r : ℂ)) (mul_integral_betaKernel_one hH)
    have hi2 := congrArg (fun r : ℝ => (r : ℂ)) (mul_sq_integral_betaKernel_succ hH 1)
    push_cast at hi1 hi2 ⊢
    have hi1' :
        ((H : ℂ) * ((H : ℂ) - 1 / 2)) * (∫ s in Ioo (0 : ℝ) 1, betaKernel H 1 s) =
          (Real.sqrt π : ℂ) * (transmuteWeight H : ℂ) := by
      linear_combination hi1
    have hi2' :
        ((H : ℂ) - 1 / 2) ^ 2 * (∫ s in Ioo (0 : ℝ) 1, betaKernel H 2 s) =
          (Real.sqrt π : ℂ) * (transmuteWeight H : ℂ) *
            ((realPochhammer (H - 1 / 2) 2 : ℂ) / (realPochhammer H 2 : ℂ)) := by
      linear_combination hi2
    rw [hi1', hi2', transmuteModeSum_zero]
    have h_ms1 : (transmuteModeSum H 1 : ℂ) =
        (realPochhammer (H - 1 / 2) 2 : ℂ) / (realPochhammer H 2 : ℂ) := by
      have h_eq := sum_transmuteCoeff_eq_of_pos hH (m := 1) le_rfl
      simp only [Finset.range_one, Finset.sum_singleton, Nat.sub_self, halfBinom_zero,
        block1dCoeff_zero, mul_one, one_mul, Nat.add_zero] at h_eq
      have h_c := congrArg (fun r : ℝ => (r : ℂ)) h_eq
      push_cast at h_c
      simpa [transmuteModeSum] using h_c
    rw [h_ms1]
    push_cast
    field_simp [h_sqrt_ne]
  · have hm_pos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    have h_reg : regTransmuteModeTerm H w m =
        fun s => ((H - 1 / 2 : ℝ) : ℂ) ^ 2 * transmuteModeTerm H w m s := by
      ext s
      dsimp [regTransmuteModeTerm]
      simp [hm]
    rw [h_reg]
    dsimp [transmuteModeTerm]
    rw [integral_const_mul, integral_const_mul,
      integral_finsetSum (Finset.range (m + 1)) fun n _ => by
        refine Integrable.const_mul (Integrable.sub ?_ ?_) _
        · have h_idx : m + n = (m + n - 1) + 1 := by omega
          rw [h_idx]
          exact (integrableOn_betaKernel_succ hH (m + n - 1)).ofReal.mul_const _
        · have h_idx : m + 2 + n = (m + 1 + n) + 1 := by omega
          rw [h_idx]
          exact (integrableOn_betaKernel_succ hH (m + 1 + n)).ofReal.mul_const _]
    rw [mul_left_comm (((H - 1 / 2 : ℝ) : ℂ) ^ 2) (Complex.exp ((H : ℂ) * w)), Finset.mul_sum]
    have h_each : ∀ n : ℕ,
        ((H - 1 / 2 : ℝ) : ℂ) ^ 2 *
          (∫ s in Ioo (0 : ℝ) 1,
            ((halfBinom (m - n) * block1dCoeff H n : ℝ) : ℂ) *
              ((betaKernel H (m + n) s : ℂ) * (Complex.exp (2 * w)) ^ m -
                (betaKernel H (m + 2 + n) s : ℂ) * (Complex.exp (2 * w)) ^ (m + 1))) =
        ((Real.sqrt π * transmuteWeight H : ℝ) : ℂ) *
          ((((halfBinom (m - n) * block1dCoeff H n *
            (realPochhammer (H - 1 / 2) (m + n) / realPochhammer H (m + n)) : ℝ) : ℂ) *
              (Complex.exp (2 * w)) ^ m) -
            (((halfBinom (m - n) * block1dCoeff H n *
              (realPochhammer (H - 1 / 2) (m + 2 + n) / realPochhammer H (m + 2 + n)) : ℝ) : ℂ) *
              (Complex.exp (2 * w)) ^ (m + 1))) := by
      intro n
      have h_idx1 : m + n = (m + n - 1) + 1 := by omega
      have h_idx2 : m + 2 + n = (m + 1 + n) + 1 := by omega
      have h1 : IntegrableOn
          (fun s : ℝ => (betaKernel H (m + n) s : ℂ) * (Complex.exp (2 * w)) ^ m)
          (Ioo (0 : ℝ) 1) volume := by
        rw [h_idx1]
        exact (integrableOn_betaKernel_succ hH (m + n - 1)).ofReal.mul_const _
      have h2 : IntegrableOn
          (fun s : ℝ => (betaKernel H (m + 2 + n) s : ℂ) * (Complex.exp (2 * w)) ^ (m + 1))
          (Ioo (0 : ℝ) 1) volume := by
        rw [h_idx2]
        exact (integrableOn_betaKernel_succ hH (m + 1 + n)).ofReal.mul_const _
      rw [integral_const_mul, integral_sub h1 h2, integral_mul_const, integral_mul_const,
        integral_complex_ofReal, integral_complex_ofReal]
      have hi1 := congrArg (fun r : ℝ => (r : ℂ))
        (mul_sq_integral_betaKernel_succ hH (m + n - 1))
      have hi2 := congrArg (fun r : ℝ => (r : ℂ))
        (mul_sq_integral_betaKernel_succ hH (m + 1 + n))
      rw [← h_idx1] at hi1
      rw [← h_idx2] at hi2
      push_cast at hi1 hi2 ⊢
      linear_combination
        ((halfBinom (m - n) : ℂ) * (block1dCoeff H n : ℂ) * (Complex.exp (2 * w)) ^ m) * hi1 -
          ((halfBinom (m - n) : ℂ) * (block1dCoeff H n : ℂ) *
            (Complex.exp (2 * w)) ^ (m + 1)) * hi2
    simp_rw [h_each, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_mul]
    have h_sum1 :
        (∑ x ∈ Finset.range (m + 1),
          ((halfBinom (m - x) * block1dCoeff H x *
            (realPochhammer (H - 1 / 2) (m + x) / realPochhammer H (m + x)) : ℝ) : ℂ)) =
        (transmuteModeSum H m : ℂ) := by
      dsimp [transmuteModeSum]
      push_cast
      rfl
    have h_sum2 :
        (∑ x ∈ Finset.range (m + 1),
          ((halfBinom (m - x) * block1dCoeff H x *
            (realPochhammer (H - 1 / 2) (m + 2 + x) / realPochhammer H (m + 2 + x)) : ℝ) : ℂ)) =
        (transmuteModeSum H (m + 1) : ℂ) := by
      have h_eq := (sum_transmuteCoeff_eq_of_pos hH (m := m + 1) (by omega)).symm
      have h_idx : ∀ x : ℕ, m + 1 + 1 + x = m + 2 + x := fun x => by omega
      simp_rw [h_idx] at h_eq
      have h_c := congrArg (fun r : ℝ => (r : ℂ)) h_eq
      push_cast at h_c
      simpa [transmuteModeSum] using h_c
    rw [h_sum1, h_sum2]
    push_cast
    field_simp [h_sqrt_ne]

/-- Dominated convergence evaluation of the regularized mode series for all $H > 0$ and
$w \in \operatorname{UcDisk}$. -/
lemma hasSum_integral_regTransmuteModeTerm {H : ℝ} (hH : 0 < H) {w : ℂ} (hw : w ∈ UcDisk) :
    HasSum
      (fun m : ℕ => ∫ s in Ioo (0 : ℝ) 1, regTransmuteModeTerm H w m s)
      (∫ s in Ioo (0 : ℝ) 1,
        (((H - 1 / 2 : ℝ) : ℂ) ^ 2 *
          (transmuteKernel w s * block1d H (w + (Real.log s : ℂ))) -
        Complex.exp ((H : ℂ) * w) *
          (((H - 1 / 2 : ℝ) : ℂ) ^ 2 * (betaKernel H 0 s : ℂ) -
            ((H * (H - 1 / 2) : ℝ) : ℂ) * (betaKernel H 1 s : ℂ)))) := by
  set bound : ℕ → ℝ → ℝ := fun m s =>
    (2 * (H + 1 / 2) ^ 2 * ((m : ℝ) + 1) *
      Real.exp (H * w.re) * (Real.exp (2 * w.re)) ^ m) *
      betaKernel H 1 s
  have h_sum_m :
      Summable (fun m : ℕ =>
        2 * (H + 1 / 2) ^ 2 * ((m : ℝ) + 1) *
          Real.exp (H * w.re) * (Real.exp (2 * w.re)) ^ m) := by
    have h1 := (summable_mul_add_one_mul_exp_pow hw).mul_left
      (2 * (H + 1 / 2) ^ 2 * Real.exp (H * w.re))
    refine h1.congr fun m => by ring
  refine MeasureTheory.hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Ioo (0 : ℝ) 1)) bound ?_ ?_ ?_ ?_ ?_
  · intro m
    exact (continuousOn_regTransmuteModeTerm H w m).aestronglyMeasurable measurableSet_Ioo
  · intro m
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact norm_regTransmuteModeTerm_le hH hw m hs
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s _
    exact h_sum_m.mul_right (betaKernel H 1 s)
  · have h_tsum :
        (fun s : ℝ => ∑' m : ℕ, bound m s) =
          fun s : ℝ =>
            (∑' m : ℕ,
              2 * (H + 1 / 2) ^ 2 * ((m : ℝ) + 1) *
                Real.exp (H * w.re) * (Real.exp (2 * w.re)) ^ m) *
              betaKernel H 1 s := by
      ext s
      dsimp [bound]
      exact tsum_mul_right
    rw [h_tsum]
    exact (integrableOn_betaKernel_succ hH 0).const_mul _
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact hasSum_regTransmuteModeTerm hH.le hw hs

/-- Integrability of the regularized Casimir RHS on `Ioo 0 1` for all $H > 0$. -/
lemma integrableOn_regTransmuteSum {H : ℝ} (hH : 0 < H) {w : ℂ} (hw : w ∈ UcDisk) :
    IntegrableOn
      (fun s : ℝ =>
        ((H - 1 / 2 : ℝ) : ℂ) ^ 2 *
          (transmuteKernel w s * block1d H (w + (Real.log s : ℂ))) -
        Complex.exp ((H : ℂ) * w) *
          (((H - 1 / 2 : ℝ) : ℂ) ^ 2 * (betaKernel H 0 s : ℂ) -
            ((H * (H - 1 / 2) : ℝ) : ℂ) * (betaKernel H 1 s : ℂ)))
      (Ioo (0 : ℝ) 1) volume := by
  set bound : ℕ → ℝ → ℝ := fun m s =>
    (2 * (H + 1 / 2) ^ 2 * ((m : ℝ) + 1) *
      Real.exp (H * w.re) * (Real.exp (2 * w.re)) ^ m) *
      betaKernel H 1 s
  have h_sum_m :
      Summable (fun m : ℕ =>
        2 * (H + 1 / 2) ^ 2 * ((m : ℝ) + 1) *
          Real.exp (H * w.re) * (Real.exp (2 * w.re)) ^ m) := by
    have h1 := (summable_mul_add_one_mul_exp_pow hw).mul_left
      (2 * (H + 1 / 2) ^ 2 * Real.exp (H * w.re))
    refine h1.congr fun m => by ring
  have h_dom_int :
      IntegrableOn (fun s : ℝ => ∑' m : ℕ, bound m s) (Ioo (0 : ℝ) 1) volume := by
    have h_tsum :
        (fun s : ℝ => ∑' m : ℕ, bound m s) =
          fun s : ℝ =>
            (∑' m : ℕ,
              2 * (H + 1 / 2) ^ 2 * ((m : ℝ) + 1) *
                Real.exp (H * w.re) * (Real.exp (2 * w.re)) ^ m) *
              betaKernel H 1 s := by
      ext s
      dsimp [bound]
      exact tsum_mul_right
    rw [h_tsum]
    exact (integrableOn_betaKernel_succ hH 0).const_mul _
  have h_meas : AEStronglyMeasurable
      (fun s : ℝ =>
        ((H - 1 / 2 : ℝ) : ℂ) ^ 2 *
          (transmuteKernel w s * block1d H (w + (Real.log s : ℂ))) -
        Complex.exp ((H : ℂ) * w) *
          (((H - 1 / 2 : ℝ) : ℂ) ^ 2 * (betaKernel H 0 s : ℂ) -
            ((H * (H - 1 / 2) : ℝ) : ℂ) * (betaKernel H 1 s : ℂ)))
      (volume.restrict (Ioo (0 : ℝ) 1)) :=
    aestronglyMeasurable_of_tendsto_ae (u := atTop)
      (f := fun N s => ∑ m ∈ Finset.range N, regTransmuteModeTerm H w m s)
      (fun N => Finset.aestronglyMeasurable_fun_sum _ fun m _ =>
        (continuousOn_regTransmuteModeTerm H w m).aestronglyMeasurable measurableSet_Ioo)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
        exact (hasSum_regTransmuteModeTerm hH.le hw hs).tendsto_sum_nat)
  refine h_dom_int.mono' h_meas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have h_hs := hasSum_regTransmuteModeTerm hH.le hw hs
  rw [← h_hs.tsum_eq]
  have h_sum_b : Summable (fun m : ℕ => bound m s) := h_sum_m.mul_right (betaKernel H 1 s)
  have h_sum_norm : Summable (fun m : ℕ => ‖regTransmuteModeTerm H w m s‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun m => norm_regTransmuteModeTerm_le hH hw m hs) h_sum_b
  exact (norm_tsum_le_tsum_norm h_sum_norm).trans
    (h_sum_norm.tsum_le_tsum (fun m => norm_regTransmuteModeTerm_le hH hw m hs) h_sum_b)

/-- Evaluation of the integral of the regularized Casimir RHS for all $H > 0$. -/
lemma inv_sqrt_pi_mul_integral_regTransmuteSum {H : ℝ} (hH : 0 < H) {w : ℂ} (hw : w ∈ UcDisk) :
    ((Real.sqrt π : ℝ) : ℂ)⁻¹ *
        (∫ s in Ioo (0 : ℝ) 1,
          (((H - 1 / 2 : ℝ) : ℂ) ^ 2 *
            (transmuteKernel w s * block1d H (w + (Real.log s : ℂ))) -
          Complex.exp ((H : ℂ) * w) *
            (((H - 1 / 2 : ℝ) : ℂ) ^ 2 * (betaKernel H 0 s : ℂ) -
              ((H * (H - 1 / 2) : ℝ) : ℂ) * (betaKernel H 1 s : ℂ)))) =
      (transmuteWeight H : ℂ) * Complex.exp ((H : ℂ) * w) := by
  have h_scaled := (hasSum_integral_regTransmuteModeTerm hH hw).mul_left
    (((Real.sqrt π : ℝ) : ℂ)⁻¹)
  set c : ℕ → ℂ := fun m => (transmuteModeSum H m : ℂ) * (Complex.exp (2 * w)) ^ m
  have hc_summable : Summable c := by
    have h_dom := (summable_mul_add_one_mul_exp_pow hw).mul_left (1 + |H - 1 / 2| / H)
    refine Summable.of_norm_bounded h_dom fun m => ?_
    dsimp [c]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow, Complex.norm_exp]
    have hre : (2 * w).re = 2 * w.re := by simp [Complex.mul_re]
    rw [hre, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (abs_transmuteModeSum_le_of_pos hH m) (by positivity)
  have hc_shift : HasSum (fun m : ℕ => c (m + 1)) ((∑' m : ℕ, c m) - c 0) := by
    simpa using (hasSum_nat_add_iff' 1).mpr hc_summable.hasSum
  have hc_tele : HasSum (fun m : ℕ => c m - c (m + 1)) 1 := by
    have h_sub := hc_summable.hasSum.sub hc_shift
    have hc0 : c 0 = 1 := by simp [c]
    rwa [sub_sub_cancel, hc0] at h_sub
  have h_tele_mul := hc_tele.mul_left ((transmuteWeight H : ℂ) * Complex.exp ((H : ℂ) * w))
  rw [mul_one] at h_tele_mul
  have h_tele_congr :
      HasSum
        (fun m : ℕ =>
          ((Real.sqrt π : ℝ) : ℂ)⁻¹ * (∫ s in Ioo (0 : ℝ) 1, regTransmuteModeTerm H w m s))
        ((transmuteWeight H : ℂ) * Complex.exp ((H : ℂ) * w)) := by
    refine h_tele_mul.congr_fun fun m => ?_
    rw [inv_sqrt_pi_mul_integral_regTransmuteModeTerm hH w m]
  exact h_scaled.unique h_tele_congr

lemma hasDerivAt_block1dDeriv2 {H : ℝ} (hH : 0 ≤ H) {z : ℂ} (hz : z ∈ UcDisk) :
    HasDerivAt (block1dDeriv2 H)
      (∑' n : ℕ, ((block1dCoeff H n * (H + 2 * (n : ℝ)) ^ 3 : ℝ) : ℂ) *
        Complex.exp (((H + 2 * (n : ℝ) : ℝ) : ℂ) * z)) z := by
  have hz_re : z.re < 0 := mem_UcDisk_iff.mp hz
  set t : Set ℂ := Metric.ball z (-z.re / 2)
  have hr : 0 < -z.re / 2 := by linarith
  have hd2_pos_sum : Summable (fun n : ℕ =>
      (H + 2) ^ 3 * ((1 + (n : ℝ)) ^ 3 * (Real.exp z.re) ^ n)) :=
    (summable_one_add_natCast_pow_mul_exp 3 hz_re).mul_left ((H + 2) ^ 3)
  have h_deriv : ∀ n : ℕ, ∀ y ∈ t,
      HasDerivAt (block1dDeriv2Term H n)
        (((block1dCoeff H n * (H + 2 * (n : ℝ)) ^ 3 : ℝ) : ℂ) *
          Complex.exp (((H + 2 * (n : ℝ) : ℝ) : ℂ) * y)) y := by
    intro n y _
    have h1 : HasDerivAt (fun u : ℂ => ((H + 2 * (n : ℝ) : ℝ) : ℂ) * u)
        ((H + 2 * (n : ℝ) : ℝ) : ℂ) y := by
      simpa using (hasDerivAt_id y).const_mul ((H + 2 * (n : ℝ) : ℝ) : ℂ)
    have h2 := h1.cexp.const_mul ((block1dCoeff H n * (H + 2 * (n : ℝ)) ^ 2 : ℝ) : ℂ)
    refine h2.congr_deriv ?_
    push_cast
    ring
  have h_bd : ∀ n : ℕ, ∀ y ∈ t,
      ‖((block1dCoeff H n * (H + 2 * (n : ℝ)) ^ 3 : ℝ) : ℂ) *
        Complex.exp (((H + 2 * (n : ℝ) : ℝ) : ℂ) * y)‖ ≤
      (H + 2) ^ 3 * ((1 + (n : ℝ)) ^ 3 * (Real.exp z.re) ^ n) := by
    intro n y hy
    have hy_re : y.re ≤ z.re / 2 := re_le_half_of_mem_ball hy
    have h_eq : 2 * (z.re / 2) = z.re := by ring
    rw [← h_eq]
    exact norm_block1dPowTerm_le hH 3 (by linarith) hy_re n
  exact hasDerivAt_tsum_of_isPreconnected hd2_pos_sum Metric.isOpen_ball
    (convex_ball z (-z.re / 2)).isPreconnected h_deriv h_bd
    (Metric.mem_ball_self hr) (summable_block1dDeriv2Term hH hz) (Metric.mem_ball_self hr)

lemma continuousOn_transmuteInner_block1d {H : ℝ} (hH : 0 ≤ H) {w : ℂ} (hw : w ∈ UcDisk) :
    ContinuousOn
      (fun s : ℝ => transmuteInnerKernel w s * transmuteInnerDiff (block1d H) w s)
      (Ioo (0 : ℝ) 1) := by
  intro s hs
  have hs0 : 0 < s := hs.1
  have hs1 : 0 < 1 - s := sub_pos.mpr hs.2
  set z : ℂ := w + (Real.log s : ℂ)
  have hz : z ∈ UcDisk := by
    rw [mem_UcDisk_iff]
    have hlog : Real.log s < 0 := Real.log_neg hs.1 hs.2
    have hre : z.re = w.re + Real.log s := by simp [z, Complex.add_re]
    linarith [mem_UcDisk_iff.mp hw]
  have h_k_cont : ContinuousAt (transmuteInnerKernel w) s := by
    have h1 : ContinuousAt (fun x : ℝ => x ^ (-1 / 2 : ℝ)) s :=
      continuousAt_id.rpow_const (Or.inl hs0.ne')
    have h2 : ContinuousAt (fun x : ℝ => (1 - x) ^ (-1 / 2 : ℝ)) s :=
      (continuousAt_const.sub continuousAt_id).rpow_const (Or.inl hs1.ne')
    have h3 : ContinuousAt
        (fun x : ℝ => (1 - (x : ℂ) * Complex.exp (2 * w)) ^ (-1 / 2 : ℂ)) s :=
      (continuousAt_const.sub
        (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)).cpow
        continuousAt_const
        (one_sub_mul_exp_two_mul_mem_slitPlane hw ⟨hs.1.le, hs.2.le⟩)
    exact (Complex.continuous_ofReal.continuousAt.comp (h1.mul h2)).mul h3
  have h_log : ContinuousAt (fun x : ℝ => w + (Real.log x : ℂ)) s :=
    continuousAt_const.add
      (Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log hs0.ne'))
  have h_ev1 : (fun x : ℝ => deriv (block1d H) (w + (Real.log x : ℂ))) =ᶠ[𝓝 s]
      (fun x : ℝ => block1dDeriv1 H (w + (Real.log x : ℂ))) := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with x hx
    have hxz : w + (Real.log x : ℂ) ∈ UcDisk := by
      rw [mem_UcDisk_iff]
      have hlog : Real.log x < 0 := Real.log_neg hx.1 hx.2
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith [mem_UcDisk_iff.mp hw]
    exact deriv_block1d hH hxz
  have h_ev2 : (fun x : ℝ => deriv (deriv (block1d H)) (w + (Real.log x : ℂ))) =ᶠ[𝓝 s]
      (fun x : ℝ => block1dDeriv2 H (w + (Real.log x : ℂ))) := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with x hx
    have hxz : w + (Real.log x : ℂ) ∈ UcDisk := by
      rw [mem_UcDisk_iff]
      have hlog : Real.log x < 0 := Real.log_neg hx.1 hx.2
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith [mem_UcDisk_iff.mp hw]
    exact deriv_deriv_block1d hH hxz
  have hd1_cont : ContinuousAt
      (fun x : ℝ => deriv (block1d H) (w + (Real.log x : ℂ))) s := by
    rw [continuousAt_congr h_ev1]
    exact ContinuousAt.comp (g := block1dDeriv1 H) (f := fun x : ℝ => w + (Real.log x : ℂ))
      (hasDerivAt_block1dDeriv1 hH hz).continuousAt h_log
  have hd2_cont : ContinuousAt
      (fun x : ℝ => deriv (deriv (block1d H)) (w + (Real.log x : ℂ))) s := by
    rw [continuousAt_congr h_ev2]
    exact ContinuousAt.comp (g := block1dDeriv2 H) (f := fun x : ℝ => w + (Real.log x : ℂ))
      (hasDerivAt_block1dDeriv2 hH hz).continuousAt h_log
  have hz_sub : 1 - (s : ℂ) * Complex.exp w ≠ 0 := one_sub_mul_exp_ne_zero hw hs
  have h_rat1 : ContinuousAt
      (fun x : ℝ => (1 + (x : ℂ) * Complex.exp w) / (1 - (x : ℂ) * Complex.exp w)) s :=
    (continuousAt_const.add
      (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)).div
      (continuousAt_const.sub
        (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)) hz_sub
  have h_rat2 : ContinuousAt
      (fun x : ℝ => 2 * (x : ℂ) * Complex.exp w / (1 - (x : ℂ) * Complex.exp w) ^ 2) s :=
    ((continuousAt_const.mul Complex.continuous_ofReal.continuousAt).mul
      continuousAt_const).div
      ((continuousAt_const.sub
        (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)).pow 2)
      (pow_ne_zero 2 hz_sub)
  have h_diff_cont : ContinuousAt (transmuteInnerDiff (block1d H) w) s := by
    unfold transmuteInnerDiff
    exact (continuousAt_const.mul ((h_rat1.mul hd2_cont).add (h_rat2.mul hd1_cont))).sub
      (continuousAt_const.mul hd1_cont)
  exact (h_k_cont.mul h_diff_cont).continuousWithinAt

/-- Integrability of `s ↦ transmuteInnerKernel w s * transmuteInnerDiff (block1d H) w s` on
`Ioo 0 1` for all $H \ge 0$ and $w \in \operatorname{UcDisk}$. -/
lemma integrableOn_transmuteInner_block1d {H : ℝ} (hH : 0 ≤ H) {w : ℂ} (hw : w ∈ UcDisk) :
    IntegrableOn
      (fun s : ℝ => transmuteInnerKernel w s * transmuteInnerDiff (block1d H) w s)
      (Ioo (0 : ℝ) 1) volume := by
  have hw_re : w.re < 0 := mem_UcDisk_iff.mp hw
  have h_sum1 : Summable (fun n : ℕ =>
      (H + 2) ^ 1 * ((1 + (n : ℝ)) ^ 1 * (Real.exp (2 * w.re)) ^ n)) :=
    (summable_one_add_natCast_pow_mul_exp 1 (by linarith : 2 * w.re < 0)).mul_left ((H + 2) ^ 1)
  have h_sum2 : Summable (fun n : ℕ =>
      (H + 2) ^ 2 * ((1 + (n : ℝ)) ^ 2 * (Real.exp (2 * w.re)) ^ n)) :=
    (summable_one_add_natCast_pow_mul_exp 2 (by linarith : 2 * w.re < 0)).mul_left ((H + 2) ^ 2)
  set D1 : ℝ := ∑' n : ℕ, (H + 2) ^ 1 * ((1 + (n : ℝ)) ^ 1 * (Real.exp (2 * w.re)) ^ n)
  set D2 : ℝ := ∑' n : ℕ, (H + 2) ^ 2 * ((1 + (n : ℝ)) ^ 2 * (Real.exp (2 * w.re)) ^ n)
  have hD1_nonneg : 0 ≤ D1 := tsum_nonneg fun _ => by positivity
  have hD2_nonneg : 0 ≤ D2 := tsum_nonneg fun _ => by positivity
  have h_1_sub_exp_pos : 0 < 1 - Real.exp w.re :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr hw_re)
  have h_1_sub_exp2_pos : 0 < 1 - Real.exp (2 * w.re) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  set C_diff : ℝ :=
    4 * (2 / (1 - Real.exp w.re) * D2 + 2 / (1 - Real.exp w.re) ^ 2 * D1) + 2 * D1
  set C_k : ℝ := (1 - Real.exp (2 * w.re)) ^ (-1 / 2 : ℝ)
  have h_dom : IntegrableOn (fun s : ℝ => (C_k * C_diff) * betaKernel 1 0 s)
      (Ioo (0 : ℝ) 1) volume :=
    (integrableOn_betaKernel (by norm_num : 1 / 2 < (1 : ℝ)) 0).const_mul (C_k * C_diff)
  refine h_dom.mono'
    ((continuousOn_transmuteInner_block1d hH hw).aestronglyMeasurable measurableSet_Ioo) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  set z : ℂ := w + (Real.log s : ℂ)
  have hlog : Real.log s < 0 := Real.log_neg hs.1 hs.2
  have hz_le : z.re ≤ w.re := by
    have hre : z.re = w.re + Real.log s := by simp [z, Complex.add_re]
    linarith
  have hz : z ∈ UcDisk := mem_UcDisk_iff.mpr (hz_le.trans_lt hw_re)
  have hd1_le : ‖deriv (block1d H) z‖ ≤ D1 := by
    rw [deriv_block1d hH hz]
    dsimp [block1dDeriv1]
    have hs1_z : Summable (fun n : ℕ => ‖block1dDeriv1Term H n z‖) :=
      (summable_block1dDeriv1Term hH hz).norm
    exact (norm_tsum_le_tsum_norm hs1_z).trans
      (hs1_z.tsum_le_tsum
        (fun n => by
          simpa [block1dDeriv1Term, pow_one] using
            norm_block1dPowTerm_le hH 1 hw_re.le hz_le n)
        h_sum1)
  have hd2_le : ‖deriv (deriv (block1d H)) z‖ ≤ D2 := by
    rw [deriv_deriv_block1d hH hz]
    dsimp [block1dDeriv2]
    have hs2_z : Summable (fun n : ℕ => ‖block1dDeriv2Term H n z‖) :=
      (summable_block1dDeriv2Term hH hz).norm
    exact (norm_tsum_le_tsum_norm hs2_z).trans
      (hs2_z.tsum_le_tsum
        (fun n => by
          simpa [block1dDeriv2Term] using
            norm_block1dPowTerm_le hH 2 hw_re.le hz_le n)
        h_sum2)
  have h_k_le : ‖transmuteInnerKernel w s‖ ≤ C_k * betaKernel 1 0 s := by
    rw [norm_transmuteInnerKernel_eq hw hs]
    have h_norm_sub : 1 - Real.exp (2 * w.re) ≤ ‖1 - (s : ℂ) * Complex.exp (2 * w)‖ := by
      have h1 := norm_sub_norm_le (1 : ℂ) ((s : ℂ) * Complex.exp (2 * w))
      rw [norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.1.le,
        Complex.norm_exp] at h1
      have hre : (2 * w).re = 2 * w.re := by simp [Complex.mul_re]
      rw [hre] at h1
      have h_le : s * Real.exp (2 * w.re) ≤ 1 * Real.exp (2 * w.re) :=
        mul_le_mul_of_nonneg_right hs.2.le (by positivity)
      linarith
    have h_rpow :
        ‖1 - (s : ℂ) * Complex.exp (2 * w)‖ ^ (-1 / 2 : ℝ) ≤ C_k :=
      Real.rpow_le_rpow_of_nonpos h_1_sub_exp2_pos h_norm_sub (by norm_num)
    have h_bk : s ^ (-1 / 2 : ℝ) * (1 - s) ^ (-1 / 2 : ℝ) = betaKernel 1 0 s := by
      dsimp [betaKernel]
      congr 2
      norm_num
    rw [h_bk, mul_comm]
    exact mul_le_mul_of_nonneg_right h_rpow (betaKernel_nonneg 1 0 hs)
  have h_diff_le : ‖transmuteInnerDiff (block1d H) w s‖ ≤ C_diff := by
    dsimp [transmuteInnerDiff]
    have hz_def : w + (Real.log s : ℂ) = z := rfl
    rw [hz_def]
    have h_sub_ge : 1 - Real.exp w.re ≤ ‖1 - (s : ℂ) * Complex.exp w‖ := by
      have h1 := norm_sub_norm_le (1 : ℂ) ((s : ℂ) * Complex.exp w)
      rw [norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.1.le,
        Complex.norm_exp] at h1
      have h_le : s * Real.exp w.re ≤ 1 * Real.exp w.re :=
        mul_le_mul_of_nonneg_right hs.2.le (by positivity)
      linarith
    have h_exp_le1 : ‖Complex.exp w‖ ≤ 1 := by
      rw [Complex.norm_exp]
      exact Real.exp_le_one_iff.mpr hw_re.le
    have h_s_exp_le1 : ‖(s : ℂ) * Complex.exp w‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.1.le]
      exact (mul_le_of_le_one_left (norm_nonneg _) hs.2.le).trans h_exp_le1
    have h_1_sub_w_le2 : ‖1 - Complex.exp w‖ ≤ 2 := by
      have h1 := norm_sub_le (1 : ℂ) (Complex.exp w)
      rw [norm_one] at h1; linarith
    have h_1_add_w_le2 : ‖1 + Complex.exp w‖ ≤ 2 := by
      have h1 := norm_add_le (1 : ℂ) (Complex.exp w)
      rw [norm_one] at h1; linarith
    have h_1_add_sw_le2 : ‖1 + (s : ℂ) * Complex.exp w‖ ≤ 2 := by
      have h1 := norm_add_le (1 : ℂ) ((s : ℂ) * Complex.exp w)
      rw [norm_one] at h1; linarith
    have h_rat1_le : ‖(1 + (s : ℂ) * Complex.exp w) / (1 - (s : ℂ) * Complex.exp w)‖ ≤
        2 / (1 - Real.exp w.re) := by
      rw [norm_div]
      exact div_le_div₀ (by norm_num) h_1_add_sw_le2 h_1_sub_exp_pos h_sub_ge
    have h_rat2_le :
        ‖2 * (s : ℂ) * Complex.exp w / (1 - (s : ℂ) * Complex.exp w) ^ 2‖ ≤
          2 / (1 - Real.exp w.re) ^ 2 := by
      rw [mul_assoc, norm_div, norm_mul, norm_pow, Complex.norm_ofNat]
      have h_num : 2 * ‖(s : ℂ) * Complex.exp w‖ ≤ 2 := by linarith
      have h_den : (1 - Real.exp w.re) ^ 2 ≤ ‖1 - (s : ℂ) * Complex.exp w‖ ^ 2 :=
        pow_le_pow_left₀ h_1_sub_exp_pos.le h_sub_ge 2
      exact div_le_div₀ (by norm_num) h_num (sq_pos_of_pos h_1_sub_exp_pos) h_den
    have h_sq1 : ‖(1 - Complex.exp w) ^ 2‖ ≤ 4 := by
      rw [norm_pow]
      have h2 : (2 : ℝ) ^ 2 = 4 := by norm_num
      rw [← h2]
      exact pow_le_pow_left₀ (norm_nonneg _) h_1_sub_w_le2 2
    have h_sq2 : ‖(1 / 2 : ℂ) * (1 + Complex.exp w) ^ 2‖ ≤ 2 := by
      have h_half : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
      rw [norm_mul, norm_pow, h_half]
      have h_pow : ‖1 + Complex.exp w‖ ^ 2 ≤ 2 ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h_1_add_w_le2 2
      linarith
    have h_p1 :
        ‖(1 + (s : ℂ) * Complex.exp w) / (1 - (s : ℂ) * Complex.exp w) *
            deriv (deriv (block1d H)) z +
          2 * (s : ℂ) * Complex.exp w / (1 - (s : ℂ) * Complex.exp w) ^ 2 *
            deriv (block1d H) z‖ ≤
        2 / (1 - Real.exp w.re) * D2 + 2 / (1 - Real.exp w.re) ^ 2 * D1 := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul]
        exact mul_le_mul h_rat1_le hd2_le (norm_nonneg _) (by positivity)
      · rw [norm_mul]
        exact mul_le_mul h_rat2_le hd1_le (norm_nonneg _) (by positivity)
    have h_p2 :
        ‖(1 / 2 : ℂ) * (1 + Complex.exp w) ^ 2 * deriv (block1d H) z‖ ≤ 2 * D1 := by
      rw [norm_mul]
      exact mul_le_mul h_sq2 hd1_le (norm_nonneg _) (by norm_num)
    refine (norm_sub_le _ _).trans (add_le_add ?_ h_p2)
    rw [norm_mul]
    exact mul_le_mul h_sq1 h_p1 (norm_nonneg _) (by norm_num)
  rw [norm_mul]
  calc
    ‖transmuteInnerKernel w s‖ * ‖transmuteInnerDiff (block1d H) w s‖
      ≤ (C_k * betaKernel 1 0 s) * C_diff :=
        mul_le_mul h_k_le h_diff_le (norm_nonneg _)
          (mul_nonneg (by positivity) (betaKernel_nonneg 1 0 hs))
    _ = (C_k * C_diff) * betaKernel 1 0 s := by ring

/-- **Main 1D Inner-Derivative Transmutation Theorem for $H > 0$
(`transmuteOpInner_block1d_of_pos`)**:
For all $H > 0$ and all $w \in \operatorname{UcDisk}$,
$$
\operatorname{transmuteOpInner}(\operatorname{block1d} H)(w)
  = (\operatorname{transmuteWeight} H : \mathbb{C}) \, e^{H w}.
$$ -/
theorem transmuteOpInner_block1d_of_pos {H : ℝ} (hH : 0 < H) {w : ℂ} (hw : w ∈ UcDisk) :
    transmuteOpInner (block1d H) w =
      (transmuteWeight H : ℂ) * Complex.exp ((H : ℂ) * w) := by
  set F : ℝ → ℂ := fun s =>
    ((H - 1 / 2 : ℝ) : ℂ) ^ 2 *
      (transmuteKernel w s * block1d H (w + (Real.log s : ℂ))) -
    Complex.exp ((H : ℂ) * w) *
      (((H - 1 / 2 : ℝ) : ℂ) ^ 2 * (betaKernel H 0 s : ℂ) -
        ((H * (H - 1 / 2) : ℝ) : ℂ) * (betaKernel H 1 s : ℂ))
  set G : ℝ → ℂ := fun s =>
    transmuteInnerKernel w s * transmuteInnerDiff (block1d H) w s
  have hF_int : IntegrableOn F (Ioo (0 : ℝ) 1) volume :=
    integrableOn_regTransmuteSum hH hw
  have hG_int : IntegrableOn G (Ioo (0 : ℝ) 1) volume :=
    integrableOn_transmuteInner_block1d hH.le hw
  have hFG_int : IntervalIntegrable (fun s : ℝ => F s - G s) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr (hF_int.sub hG_int)
  have h_deriv : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt (transmuteRegBoundary H w) (F s - G s) s := by
    intro s hs
    refine (hasDerivAt_transmuteRegBoundary hH.le hw hs).congr_deriv ?_
    dsimp [F, G]
    ring
  have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
    h_deriv hFG_int
    (tendsto_transmuteRegBoundary_zero hH hw)
    (tendsto_transmuteRegBoundary_one hH.le hw)
  rw [sub_zero, intervalIntegral.integral_of_le zero_le_one,
    MeasureTheory.integral_Ioc_eq_integral_Ioo,
    integral_sub hF_int hG_int, sub_eq_zero] at h_ftc
  dsimp [transmuteOpInner]
  change ((Real.sqrt π : ℝ) : ℂ)⁻¹ * (∫ s in Ioo (0 : ℝ) 1, G s) = _
  rw [← h_ftc]
  exact inv_sqrt_pi_mul_integral_regTransmuteSum hH hw

/-- **Action of `transmuteOpInner` on `block1d H` for All $H \ge 0$ (`transmuteOpInner_block1d`)**:
For all $H \ge 0$ and all $w \in \operatorname{UcDisk}$,
$$
\operatorname{transmuteOpInner}(\operatorname{block1d} H)(w) =
  \begin{cases}
    0 & \text{if } H = 0, \\
    \operatorname{transmuteWeight}(H) \, e^{H w} & \text{if } H > 0.
  \end{cases}
$$ -/
theorem transmuteOpInner_block1d {H : ℝ} (hH : 0 ≤ H) {w : ℂ} (hw : w ∈ UcDisk) :
    transmuteOpInner (block1d H) w =
      if H = 0 then 0 else (transmuteWeight H : ℂ) * Complex.exp ((H : ℂ) * w) := by
  split_ifs with h0
  · subst h0
    exact transmuteOpInner_block1d_zero w
  · exact transmuteOpInner_block1d_of_pos (lt_of_le_of_ne hH (Ne.symm h0)) hw

/-- For $H > 1/2$ and $w \in \operatorname{UcDisk}$, `transmuteOpInner` and `transmuteOp` agree on
`block1d H`. -/
theorem transmuteOpInner_block1d_eq_transmuteOp {H : ℝ} (hH : 1 / 2 < H)
    {w : ℂ} (hw : w ∈ UcDisk) :
    transmuteOpInner (block1d H) w = transmuteOp (block1d H) w := by
  rw [transmuteOpInner_block1d_of_pos (by linarith : 0 < H) hw,
    transmuteOp_block1d hH hw]
