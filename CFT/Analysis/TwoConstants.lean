/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Balt van Rees
-/
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Nevanlinna's Two-Constants Theorem on a Vertical Strip

This file formalizes Nevanlinna's Two-Constants Theorem on a vertical strip
$\sigma \in [\sigma_-, \sigma_+]$ ($\sigma_- < \sigma_+$) and its specialization to the strip
$[1 - 2A, -1]$ at the midpoint $\sigma = -A$ for $|t| \le T$.

## Mathematical Overview

1. **Normalized Half-Strip Majorant**:
   On the open upper half-plane $\{\zeta \in \mathbb{C} \mid \operatorname{Im}\zeta > 0\}$, the
   function
   $$\Omega(\zeta) = -\frac{2i}{\pi} \log\!\left(\frac{1 + e^{i\zeta}}{1 - e^{i\zeta}}\right)$$
   is holomorphic (since $\|e^{i\zeta}\| = e^{-\operatorname{Im}\zeta} < 1$ implies
   $\operatorname{Re}\frac{1 + e^{i\zeta}}{1 - e^{i\zeta}} > 0$), and its real part is
   $$\operatorname{Re}\Omega(x + iy) = \frac{2}{\pi} \arctan\!\left(\frac{\sin x}{\sinh y}\right).$$

2. **The $+i\eta$ Shift and Maximum Modulus on $[0, \pi] \times [0, Y]$**:
   Shifting by $+i\eta$ ($\eta > 0$) avoids the corner singularities at $(0, 0)$ and $(\pi, 0)$, so
   $\zeta \mapsto \Omega(\zeta + i\eta)$ is holomorphic on a neighborhood of the closed rectangle
   $[0, \pi] \times [0, Y]$. Applying `Complex.norm_le_of_forall_mem_frontier_norm_le` to
   $f(\zeta) \exp(\log(M/\delta)\,\Omega(\zeta + i\eta))$ and taking $Y \to +\infty$ followed by
   $\eta \to 0^+$ yields the Two-Constants bound for $y > 0$. The holomorphic reflection
   $\zeta \mapsto \pi - \zeta$ extends the bound to $y < 0$, and real affine rescaling extends it
   to any vertical strip $[\sigma_-, \sigma_+]$.
-/

open Real Complex Topology Set Metric Filter
open scoped ComplexConjugate

/-!
## Part 1: Elementary Properties of `sinh` and `harmonicMajorantRe`
-/

lemma sinh_pos_of_pos {y : ℝ} (hy : 0 < y) : 0 < Real.sinh y := by
  rw [Real.sinh_eq]
  have h1 : Real.exp (-y) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h2 : 1 < Real.exp y := Real.one_lt_exp_iff.mpr hy
  linarith

lemma sinh_mono {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) : Real.sinh y₁ ≤ Real.sinh y₂ := by
  rw [Real.sinh_eq, Real.sinh_eq]
  have h1 : Real.exp y₁ ≤ Real.exp y₂ := Real.exp_le_exp.mpr hy
  have h2 : Real.exp (-y₂) ≤ Real.exp (-y₁) := Real.exp_le_exp.mpr (by linarith)
  linarith

lemma tendsto_sinh_atTop : Tendsto Real.sinh atTop atTop := by
  have h_ev : ∀ᶠ y : ℝ in atTop, (Real.exp y - 1) / 2 ≤ Real.sinh y := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
    rw [Real.sinh_eq]
    have h1 : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have h_lim : Tendsto (fun y : ℝ => (Real.exp y - 1) / 2) atTop atTop :=
    (Real.tendsto_exp_atTop.atTop_add tendsto_const_nhds).atTop_div_const (by positivity)
  exact tendsto_atTop_mono' atTop h_ev h_lim

/-- Auxiliary smooth expression for the normalized strip harmonic measure on the open upper
half-strip $x \in [0, \pi]$, $y > 0$:
$$\omega(x, y) = \frac{2}{\pi} \arctan\!\left(\frac{\sin x}{\sinh y}\right).$$ -/
noncomputable def harmonicMajorantRe (x y : ℝ) : ℝ :=
  (2 / π) * Real.arctan (Real.sin x / Real.sinh y)

/-- Normalized harmonic measure on the strip $x \in [0, \pi]$, $y \in \mathbb{R}$, of the
horizontal segment $[0, \pi] \times \{0\}$:
$$\omega_{\mathrm{norm}}(x, y) = \begin{cases}
  1 & \text{if } y = 0, \\
  \frac{2}{\pi} \arctan\!\left(\frac{\sin x}{\sinh |y|}\right) & \text{if } y \ne 0.
\end{cases}$$ -/
noncomputable def stripHarmonicMeasureNormalized (x y : ℝ) : ℝ :=
  if y = 0 then 1 else (2 / π) * Real.arctan (Real.sin x / Real.sinh |y|)

lemma stripHarmonicMeasureNormalized_of_pos {x y : ℝ} (hy : 0 < y) :
    stripHarmonicMeasureNormalized x y = harmonicMajorantRe x y := by
  unfold stripHarmonicMeasureNormalized harmonicMajorantRe
  rw [ite_eq_right_iff.mpr (fun h => absurd h (ne_of_gt hy)), abs_of_pos hy]

lemma stripHarmonicMeasureNormalized_neg (x y : ℝ) :
    stripHarmonicMeasureNormalized x (-y) = stripHarmonicMeasureNormalized x y := by
  unfold stripHarmonicMeasureNormalized
  simp [neg_eq_zero, abs_neg]

lemma stripHarmonicMeasureNormalized_pi_sub (x y : ℝ) :
    stripHarmonicMeasureNormalized (π - x) y = stripHarmonicMeasureNormalized x y := by
  unfold stripHarmonicMeasureNormalized
  rw [Real.sin_pi_sub]

lemma harmonicMajorantRe_zero_left (y : ℝ) : harmonicMajorantRe 0 y = 0 := by
  simp [harmonicMajorantRe]

lemma harmonicMajorantRe_pi_left (y : ℝ) : harmonicMajorantRe π y = 0 := by
  simp [harmonicMajorantRe]

lemma harmonicMajorantRe_nonneg {x y : ℝ} (hx : x ∈ Icc 0 π) (hy : 0 < y) :
    0 ≤ harmonicMajorantRe x y := by
  unfold harmonicMajorantRe
  apply mul_nonneg (by positivity)
  rw [Real.arctan_nonneg]
  exact div_nonneg (Real.sin_nonneg_of_mem_Icc hx) (sinh_pos_of_pos hy).le

lemma harmonicMajorantRe_le_one (x y : ℝ) : harmonicMajorantRe x y ≤ 1 := by
  unfold harmonicMajorantRe
  have h_lt : Real.arctan (Real.sin x / Real.sinh y) < π / 2 :=
    Real.arctan_lt_pi_div_two _
  have hpi : 0 < π := Real.pi_pos
  calc (2 / π) * Real.arctan (Real.sin x / Real.sinh y)
      ≤ (2 / π) * (π / 2) := by gcongr
    _ = 1 := by field_simp

lemma harmonicMajorantRe_lt_one (x y : ℝ) : harmonicMajorantRe x y < 1 := by
  unfold harmonicMajorantRe
  have h_lt : Real.arctan (Real.sin x / Real.sinh y) < π / 2 :=
    Real.arctan_lt_pi_div_two _
  have hpi : 0 < π := Real.pi_pos
  calc (2 / π) * Real.arctan (Real.sin x / Real.sinh y)
      < (2 / π) * (π / 2) := mul_lt_mul_of_pos_left h_lt (by positivity)
    _ = 1 := by field_simp

lemma harmonicMajorantRe_le_pi_div_two (x : ℝ) {y : ℝ} (hy : 0 < y) :
    harmonicMajorantRe x y ≤ harmonicMajorantRe (π / 2) y := by
  unfold harmonicMajorantRe
  have hpi : 0 ≤ 2 / π := by positivity
  have hsinh : 0 < Real.sinh y := sinh_pos_of_pos hy
  apply mul_le_mul_of_nonneg_left _ hpi
  apply Real.arctan_strictMono.monotone
  rw [Real.sin_pi_div_two]
  exact div_le_div_of_nonneg_right (Real.sin_le_one x) hsinh.le

lemma harmonicMajorantRe_anti_right {x y₁ y₂ : ℝ} (hx : x ∈ Icc 0 π)
    (hy₁ : 0 < y₁) (hy : y₁ ≤ y₂) :
    harmonicMajorantRe x y₂ ≤ harmonicMajorantRe x y₁ := by
  unfold harmonicMajorantRe
  have hpi : 0 ≤ 2 / π := by positivity
  have hsin : 0 ≤ Real.sin x := Real.sin_nonneg_of_mem_Icc hx
  have hsinh₁ : 0 < Real.sinh y₁ := sinh_pos_of_pos hy₁
  have hsinh_le : Real.sinh y₁ ≤ Real.sinh y₂ := sinh_mono hy
  apply mul_le_mul_of_nonneg_left _ hpi
  apply Real.arctan_strictMono.monotone
  exact div_le_div_of_nonneg_left hsin hsinh₁ hsinh_le

/-!
## Part 2: Holomorphic Harmonic Majorant on the Upper Half-Plane
-/

/-- Holomorphic harmonic majorant on the upper half-plane
$\{\zeta \in \mathbb{C} \mid \operatorname{Im}\zeta > 0\}$ whose real part equals
`harmonicMajorantRe ζ.re ζ.im`:
$$\Omega(\zeta) = -\frac{2i}{\pi} \log\!\left(\frac{1 + e^{i\zeta}}{1 - e^{i\zeta}}\right).$$ -/
noncomputable def harmonicMajorantHolomorphic (ζ : ℂ) : ℂ :=
  -(2 / (π : ℂ)) * I *
    Complex.log ((1 + Complex.exp (I * ζ)) / (1 - Complex.exp (I * ζ)))

lemma norm_exp_I_mul_lt_one {ζ : ℂ} (hζ : 0 < ζ.im) :
    ‖Complex.exp (I * ζ)‖ < 1 := by
  rw [Complex.norm_exp, mul_re, I_re, I_im]
  simp only [zero_mul, one_mul, zero_sub, Real.exp_lt_one_iff, Left.neg_neg_iff]
  exact hζ

lemma one_sub_exp_I_mul_ne_zero {ζ : ℂ} (hζ : 0 < ζ.im) :
    1 - Complex.exp (I * ζ) ≠ 0 := by
  intro h
  have h_eq : Complex.exp (I * ζ) = 1 := (sub_eq_zero.mp h).symm
  have h_norm : ‖Complex.exp (I * ζ)‖ = 1 := by rw [h_eq, norm_one]
  linarith [norm_exp_I_mul_lt_one hζ]

lemma re_mobius_exp_I_mul {ζ : ℂ} :
    ((1 + Complex.exp (I * ζ)) / (1 - Complex.exp (I * ζ))).re =
      2 * Real.exp (-ζ.im) * Real.sinh ζ.im /
        Complex.normSq (1 - Complex.exp (I * ζ)) := by
  set q := Complex.exp (I * ζ)
  have h_re : ((1 + q) / (1 - q)).re =
      (1 - Complex.normSq q) / Complex.normSq (1 - q) := by
    rw [Complex.div_re]
    dsimp [Complex.normSq]
    ring
  rw [h_re]
  congr 1
  have hq_sq : Complex.normSq q = Real.exp (-2 * ζ.im) := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp, mul_re, I_re, I_im]
    simp only [zero_mul, one_mul, zero_sub]
    rw [← Real.exp_nat_mul]
    ring_nf
  rw [hq_sq, Real.sinh_eq]
  have h1 : Real.exp (-ζ.im) * Real.exp ζ.im = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h2 : Real.exp (-ζ.im) * Real.exp (-ζ.im) = Real.exp (-2 * ζ.im) := by
    rw [← Real.exp_add]
    ring_nf
  linarith

lemma im_mobius_exp_I_mul {ζ : ℂ} :
    ((1 + Complex.exp (I * ζ)) / (1 - Complex.exp (I * ζ))).im =
      2 * Real.exp (-ζ.im) * Real.sin ζ.re /
        Complex.normSq (1 - Complex.exp (I * ζ)) := by
  set q := Complex.exp (I * ζ)
  have h_im : ((1 + q) / (1 - q)).im =
      2 * q.im / Complex.normSq (1 - q) := by
    rw [Complex.div_im]
    dsimp [Complex.normSq]
    ring
  rw [h_im]
  congr 1
  have hq_im : q.im = Real.exp (-ζ.im) * Real.sin ζ.re := by
    dsimp [q]
    rw [Complex.exp_im, mul_re, mul_im, I_re, I_im]
    simp
  rw [hq_im]
  ring

lemma re_mobius_exp_I_mul_pos {ζ : ℂ} (hζ : 0 < ζ.im) :
    0 < ((1 + Complex.exp (I * ζ)) / (1 - Complex.exp (I * ζ))).re := by
  rw [re_mobius_exp_I_mul]
  have hsinh : 0 < Real.sinh ζ.im := sinh_pos_of_pos hζ
  have h_denom : 0 < Complex.normSq (1 - Complex.exp (I * ζ)) :=
    Complex.normSq_pos.mpr (one_sub_exp_I_mul_ne_zero hζ)
  positivity

lemma mobius_exp_I_mul_mem_slitPlane {ζ : ℂ} (hζ : 0 < ζ.im) :
    (1 + Complex.exp (I * ζ)) / (1 - Complex.exp (I * ζ)) ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (re_mobius_exp_I_mul_pos hζ))

lemma differentiableAt_harmonicMajorantHolomorphic {ζ : ℂ} (hζ : 0 < ζ.im) :
    DifferentiableAt ℂ harmonicMajorantHolomorphic ζ := by
  unfold harmonicMajorantHolomorphic
  have h_exp : DifferentiableAt ℂ (fun z => Complex.exp (I * z)) ζ :=
    Complex.differentiableAt_exp.comp ζ (differentiableAt_id.const_mul I)
  have h_mob : DifferentiableAt ℂ
      (fun z => (1 + Complex.exp (I * z)) / (1 - Complex.exp (I * z))) ζ :=
    (h_exp.const_add 1).div (h_exp.const_sub 1) (one_sub_exp_I_mul_ne_zero hζ)
  have h_log : DifferentiableAt ℂ
      (fun z => Complex.log ((1 + Complex.exp (I * z)) / (1 - Complex.exp (I * z)))) ζ :=
    h_mob.clog (mobius_exp_I_mul_mem_slitPlane hζ)
  exact h_log.const_mul (-(2 / (π : ℂ)) * I)

lemma arg_eq_arctan_of_re_pos {w : ℂ} (hw : 0 < w.re) :
    w.arg = Real.arctan (w.im / w.re) := by
  have hw_ne : w ≠ 0 := by
    intro h
    rw [h, zero_re] at hw
    exact lt_irrefl 0 hw
  have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw_ne
  have him_lt : |w.im| < ‖w‖ := by
    rw [← sq_lt_sq₀ (abs_nonneg w.im) hnorm.le, sq_abs,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    nlinarith [hw]
  have hdiv_lt : |w.im / ‖w‖| < 1 := by
    rw [abs_div, abs_of_pos hnorm, div_lt_one hnorm]
    exact him_lt
  have hdiv_mem : w.im / ‖w‖ ∈ Ioo (-1 : ℝ) 1 := abs_lt.mp hdiv_lt
  have harg_eq : w.arg = Real.arcsin (w.im / ‖w‖) :=
    Complex.arg_of_re_nonneg hw.le
  have harg_lt : w.arg < π / 2 := by
    rw [harg_eq, Real.arcsin_lt_pi_div_two]
    exact hdiv_mem.2
  have harg_gt : -(π / 2) < w.arg := by
    rw [harg_eq, Real.neg_pi_div_two_lt_arcsin]
    exact hdiv_mem.1
  rw [← Complex.tan_arg w, Real.arctan_tan harg_gt harg_lt]

lemma re_harmonicMajorantHolomorphic {ζ : ℂ} (hζ : 0 < ζ.im) :
    (harmonicMajorantHolomorphic ζ).re = harmonicMajorantRe ζ.re ζ.im := by
  unfold harmonicMajorantHolomorphic harmonicMajorantRe
  set w := (1 + Complex.exp (I * ζ)) / (1 - Complex.exp (I * ζ))
  have h_re_mul : (-(2 / (π : ℂ)) * I * Complex.log w).re =
      (2 / π) * (Complex.log w).im := by
    have hpi : (2 / (π : ℂ)) = ((2 / π : ℝ) : ℂ) := by push_cast; rfl
    rw [hpi]
    simp [Complex.mul_re, Complex.mul_im]
  rw [h_re_mul, Complex.log_im, arg_eq_arctan_of_re_pos (re_mobius_exp_I_mul_pos hζ)]
  congr 2
  rw [im_mobius_exp_I_mul, re_mobius_exp_I_mul]
  have h_denom : Complex.normSq (1 - Complex.exp (I * ζ)) ≠ 0 :=
    (Complex.normSq_pos.mpr (one_sub_exp_I_mul_ne_zero hζ)).ne'
  have h_exp : 2 * Real.exp (-ζ.im) ≠ 0 := by positivity
  rw [div_div_div_cancel_right₀ h_denom, mul_div_mul_left _ _ h_exp]

/-!
## Part 3: The $+i\eta$ Shift and Maximum Modulus on $[0, \pi] \times [0, Y]$
-/

/-- Open rectangle $(0, \pi) \times (0, Y)$ in $\mathbb{C}$. -/
def rectOpen (Y : ℝ) : Set ℂ :=
  {z : ℂ | z.re ∈ Ioo 0 π ∧ z.im ∈ Ioo 0 Y}

/-- Closed rectangle $[0, \pi] \times [0, Y]$ in $\mathbb{C}$. -/
def rectClosed (Y : ℝ) : Set ℂ :=
  {z : ℂ | z.re ∈ Icc 0 π ∧ z.im ∈ Icc 0 Y}

lemma isOpen_rectOpen (Y : ℝ) : IsOpen (rectOpen Y) :=
  (isOpen_Ioo.preimage Complex.continuous_re).inter
    (isOpen_Ioo.preimage Complex.continuous_im)

lemma isClosed_rectClosed (Y : ℝ) : IsClosed (rectClosed Y) :=
  (isClosed_Icc.preimage Complex.continuous_re).inter
    (isClosed_Icc.preimage Complex.continuous_im)

lemma rectOpen_subset_rectClosed (Y : ℝ) : rectOpen Y ⊆ rectClosed Y :=
  fun _ hz => ⟨Ioo_subset_Icc_self hz.1, Ioo_subset_Icc_self hz.2⟩

lemma closure_rectOpen_subset_rectClosed (Y : ℝ) :
    closure (rectOpen Y) ⊆ rectClosed Y :=
  closure_minimal (rectOpen_subset_rectClosed Y) (isClosed_rectClosed Y)

lemma isBounded_rectOpen {Y : ℝ} (hY : 0 ≤ Y) : Bornology.IsBounded (rectOpen Y) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨π + Y, fun z hz => ?_⟩
  have hre : |z.re| ≤ π := abs_le.mpr ⟨by linarith [hz.1.1, Real.pi_pos], hz.1.2.le⟩
  have him : |z.im| ≤ Y := abs_le.mpr ⟨by linarith [hz.2.1, hY], hz.2.2.le⟩
  linarith [Complex.norm_le_abs_re_add_abs_im z]

lemma mem_frontier_rectOpen_cases {Y : ℝ} {z : ℂ} (hz : z ∈ frontier (rectOpen Y)) :
    z ∈ rectClosed Y ∧ (z.re = 0 ∨ z.re = π ∨ z.im = 0 ∨ z.im = Y) := by
  rw [frontier, (isOpen_rectOpen Y).interior_eq] at hz
  have hcl : z ∈ rectClosed Y := closure_rectOpen_subset_rectClosed Y hz.1
  refine ⟨hcl, ?_⟩
  have hnot : ¬ (0 < z.re ∧ z.re < π ∧ 0 < z.im ∧ z.im < Y) := by
    intro h
    exact hz.2 ⟨⟨h.1, h.2.1⟩, ⟨h.2.2.1, h.2.2.2⟩⟩
  rcases eq_or_lt_of_le hcl.1.1 with h1 | h1
  · exact Or.inl h1.symm
  rcases eq_or_lt_of_le hcl.1.2 with h2 | h2
  · exact Or.inr (Or.inl h2)
  rcases eq_or_lt_of_le hcl.2.1 with h3 | h3
  · exact Or.inr (Or.inr (Or.inl h3.symm))
  rcases eq_or_lt_of_le hcl.2.2 with h4 | h4
  · exact Or.inr (Or.inr (Or.inr h4))
  exact absurd ⟨h1, h2, h3, h4⟩ hnot

/-- The auxiliary holomorphic function on the rectangle with $+i\eta$ shift:
$$g_\eta(\zeta) = f(\zeta) \exp\bigl(L \, \Omega(\zeta + i\eta)\bigr).$$ -/
noncomputable def shiftedMajorantAux (f : ℂ → ℂ) (L η : ℝ) (ζ : ℂ) : ℂ :=
  f ζ * Complex.exp ((L : ℂ) * harmonicMajorantHolomorphic (ζ + (η : ℂ) * I))

lemma norm_shiftedMajorantAux (f : ℂ → ℂ) (L : ℝ) {η : ℝ} {ζ : ℂ}
    (h_im : 0 < ζ.im + η) :
    ‖shiftedMajorantAux f L η ζ‖ =
      ‖f ζ‖ * Real.exp (L * harmonicMajorantRe ζ.re (ζ.im + η)) := by
  unfold shiftedMajorantAux
  rw [norm_mul, Complex.norm_exp]
  congr 2
  have hζ_im : 0 < (ζ + (η : ℂ) * I).im := by
    simp [add_im, mul_im, h_im]
  have h_re_shift : (ζ + (η : ℂ) * I).re = ζ.re := by simp
  have h_im_shift : (ζ + (η : ℂ) * I).im = ζ.im + η := by simp
  rw [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
    re_harmonicMajorantHolomorphic hζ_im, h_re_shift, h_im_shift]

lemma diffContOnCl_shiftedMajorantAux {f : ℂ → ℂ} (L : ℝ) {η Y : ℝ} (hη : 0 < η)
    (hf_diff : DifferentiableOn ℂ f {z : ℂ | z.re ∈ Ioo 0 π})
    (hf_cont : ContinuousOn f {z : ℂ | z.re ∈ Icc 0 π}) :
    DiffContOnCl ℂ (shiftedMajorantAux f L η) (rectOpen Y) := by
  have hf_dc : DiffContOnCl ℂ f (rectOpen Y) :=
    ⟨hf_diff.mono (fun z hz => hz.1),
     hf_cont.mono (fun z hz => (closure_rectOpen_subset_rectClosed Y hz).1)⟩
  have h_exp_diff : ∀ z ∈ closure (rectOpen Y),
      DifferentiableAt ℂ
        (fun w : ℂ =>
          Complex.exp ((L : ℂ) * harmonicMajorantHolomorphic (w + (η : ℂ) * I))) z := by
    intro z hz
    have hz_cl := closure_rectOpen_subset_rectClosed Y hz
    have h_im : 0 < (z + (η : ℂ) * I).im := by
      simp only [add_im, ofReal_re, mul_im, I_re, mul_zero, ofReal_im, I_im, mul_one, add_zero]
      linarith [hz_cl.2.1]
    have h_shift : DifferentiableAt ℂ (fun w : ℂ => w + (η : ℂ) * I) z :=
      differentiableAt_id.add (differentiableAt_const _)
    have h_om : DifferentiableAt ℂ
        (fun w : ℂ => harmonicMajorantHolomorphic (w + (η : ℂ) * I)) z :=
      show DifferentiableAt ℂ
          (harmonicMajorantHolomorphic ∘ fun w : ℂ => w + (η : ℂ) * I) z from
        (differentiableAt_harmonicMajorantHolomorphic h_im).comp z h_shift
    exact Complex.differentiableAt_exp.comp z (h_om.const_mul (L : ℂ))
  have h_exp_dc : DiffContOnCl ℂ
      (fun w : ℂ => Complex.exp ((L : ℂ) * harmonicMajorantHolomorphic (w + (η : ℂ) * I)))
      (rectOpen Y) :=
    ⟨fun z hz => (h_exp_diff z (subset_closure hz)).differentiableWithinAt,
     fun z hz => (h_exp_diff z hz).continuousAt.continuousWithinAt⟩
  exact ⟨hf_dc.1.mul h_exp_dc.1, hf_dc.2.mul h_exp_dc.2⟩

/-- Rectangle bound with $+i\eta$ shift on $(0, \pi) \times (0, Y)$. -/
lemma norm_shiftedMajorantAux_le_on_rect {f : ℂ → ℂ} {M δ η Y : ℝ}
    (hδ : 0 < δ) (hδM : δ ≤ M) (hη : 0 < η) (hY : 0 < Y)
    (hf_diff : DifferentiableOn ℂ f {z : ℂ | z.re ∈ Ioo 0 π})
    (hf_cont : ContinuousOn f {z : ℂ | z.re ∈ Icc 0 π})
    (hM_bound : ∀ x ∈ Icc 0 π, ∀ y : ℝ, ‖f ((x : ℂ) + (y : ℂ) * I)‖ ≤ M)
    (hδ_bound : ∀ x ∈ Icc 0 π, ‖f (x : ℂ)‖ ≤ δ)
    {x y : ℝ} (hx : x ∈ Ioo 0 π) (hy : y ∈ Ioo 0 Y) :
    ‖f ((x : ℂ) + (y : ℂ) * I)‖ *
        Real.exp (Real.log (M / δ) * harmonicMajorantRe x (y + η)) ≤
      M * Real.exp (Real.log (M / δ) * harmonicMajorantRe (π / 2) (Y + η)) := by
  set L := Real.log (M / δ)
  have hM_pos : 0 < M := lt_of_lt_of_le hδ hδM
  have hL_nonneg : 0 ≤ L := Real.log_nonneg ((one_le_div hδ).mpr hδM)
  set C := M * Real.exp (L * harmonicMajorantRe (π / 2) (Y + η))
  have hM_le_C : M ≤ C := by
    dsimp [C]
    have h_om_nonneg : 0 ≤ harmonicMajorantRe (π / 2) (Y + η) := by
      apply harmonicMajorantRe_nonneg ⟨by positivity, by linarith [Real.pi_pos]⟩ (by linarith)
    have h_exp : 1 ≤ Real.exp (L * harmonicMajorantRe (π / 2) (Y + η)) :=
      Real.one_le_exp (mul_nonneg hL_nonneg h_om_nonneg)
    nlinarith
  have h_front : ∀ z ∈ frontier (rectOpen Y), ‖shiftedMajorantAux f L η z‖ ≤ C := by
    intro z hz
    obtain ⟨hz_cl, h_side⟩ := mem_frontier_rectOpen_cases hz
    have hz_im_pos : 0 < z.im + η := by linarith [hz_cl.2.1]
    rw [norm_shiftedMajorantAux f L hz_im_pos]
    have hf_z : ‖f z‖ = ‖f ((z.re : ℂ) + (z.im : ℂ) * I)‖ := by
      rw [Complex.re_add_im]
    rcases h_side with hre0 | hre_pi | him0 | himY
    · rw [hre0, harmonicMajorantRe_zero_left, mul_zero, Real.exp_zero, mul_one, hf_z]
      exact (hM_bound z.re hz_cl.1 z.im).trans hM_le_C
    · rw [hre_pi, harmonicMajorantRe_pi_left, mul_zero, Real.exp_zero, mul_one, hf_z]
      exact (hM_bound z.re hz_cl.1 z.im).trans hM_le_C
    · have hf_real : ‖f z‖ = ‖f (z.re : ℂ)‖ := by
        rw [hf_z, him0, ofReal_zero, zero_mul, add_zero]
      rw [hf_real, him0, zero_add]
      have h_om_le : L * harmonicMajorantRe z.re η ≤ L := by
        calc L * harmonicMajorantRe z.re η ≤ L * 1 :=
              mul_le_mul_of_nonneg_left (harmonicMajorantRe_le_one z.re η) hL_nonneg
          _ = L := mul_one L
      have h_exp_le : Real.exp (L * harmonicMajorantRe z.re η) ≤ M / δ := by
        calc Real.exp (L * harmonicMajorantRe z.re η)
            ≤ Real.exp L := Real.exp_le_exp.mpr h_om_le
          _ = M / δ := Real.exp_log (div_pos hM_pos hδ)
      calc ‖f (z.re : ℂ)‖ * Real.exp (L * harmonicMajorantRe z.re η)
          ≤ δ * (M / δ) := mul_le_mul (hδ_bound z.re hz_cl.1) h_exp_le (by positivity) hδ.le
        _ = M := mul_div_cancel₀ M hδ.ne'
        _ ≤ C := hM_le_C
    · rw [himY, hf_z]
      have h_om_le : harmonicMajorantRe z.re (Y + η) ≤ harmonicMajorantRe (π / 2) (Y + η) :=
        harmonicMajorantRe_le_pi_div_two z.re (by linarith)
      have h_exp_le : Real.exp (L * harmonicMajorantRe z.re (Y + η)) ≤
          Real.exp (L * harmonicMajorantRe (π / 2) (Y + η)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h_om_le hL_nonneg)
      exact mul_le_mul (hM_bound z.re hz_cl.1 z.im) h_exp_le (by positivity) hM_pos.le
  set z₀ : ℂ := (x : ℂ) + (y : ℂ) * I
  have hz₀_mem : z₀ ∈ rectOpen Y := by
    refine ⟨?_, ?_⟩ <;> simp [z₀, hx.1, hx.2, hy.1, hy.2]
  have h_max := Complex.norm_le_of_forall_mem_frontier_norm_le
    (isBounded_rectOpen hY.le)
    (diffContOnCl_shiftedMajorantAux L hη hf_diff hf_cont)
    h_front
    (subset_closure hz₀_mem)
  have hz₀_re : z₀.re = x := by simp [z₀]
  have hz₀_im : z₀.im = y := by simp [z₀]
  have hz₀_im_pos : 0 < z₀.im + η := by linarith [hy.1, hz₀_im]
  rw [norm_shiftedMajorantAux f L hz₀_im_pos, hz₀_re, hz₀_im] at h_max
  exact h_max

/-- Taking $Y \to +\infty$ and then $\eta \to 0^+$ yields the Two-Constants bound on the open
upper half-strip $x \in (0, \pi)$, $y > 0$. -/
lemma norm_le_two_constants_normalized_pos {f : ℂ → ℂ} {M δ : ℝ}
    (hδ : 0 < δ) (hδM : δ ≤ M)
    (hf_diff : DifferentiableOn ℂ f {z : ℂ | z.re ∈ Ioo 0 π})
    (hf_cont : ContinuousOn f {z : ℂ | z.re ∈ Icc 0 π})
    (hM_bound : ∀ x ∈ Icc 0 π, ∀ y : ℝ, ‖f ((x : ℂ) + (y : ℂ) * I)‖ ≤ M)
    (hδ_bound : ∀ x ∈ Icc 0 π, ‖f (x : ℂ)‖ ≤ δ)
    {x y : ℝ} (hx : x ∈ Icc 0 π) (hy : 0 < y) :
    ‖f ((x : ℂ) + (y : ℂ) * I)‖ ≤
      M ^ (1 - harmonicMajorantRe x y) * δ ^ (harmonicMajorantRe x y) := by
  have hM_pos : 0 < M := lt_of_lt_of_le hδ hδM
  set L := Real.log (M / δ)
  suffices h_prod :
      ‖f ((x : ℂ) + (y : ℂ) * I)‖ * Real.exp (L * harmonicMajorantRe x y) ≤ M by
    set ω := harmonicMajorantRe x y
    have h_le : ‖f ((x : ℂ) + (y : ℂ) * I)‖ ≤ M * Real.exp (-(L * ω)) := by
      rw [Real.exp_neg]
      exact (le_mul_inv_iff₀ (Real.exp_pos _)).mpr h_prod
    have h_rhs : M * Real.exp (-(L * ω)) = M ^ (1 - ω) * δ ^ ω := by
      rw [Real.rpow_def_of_pos hM_pos, Real.rpow_def_of_pos hδ, ← Real.exp_add]
      have hM_exp : M = Real.exp (Real.log M) := (Real.exp_log hM_pos).symm
      conv_lhs => rw [hM_exp]
      rw [← Real.exp_add]
      congr 1
      dsimp [L]
      rw [Real.log_div hM_pos.ne' hδ.ne']
      ring
    linarith
  rcases eq_or_lt_of_le hx.1 with rfl | hx_pos
  · rw [harmonicMajorantRe_zero_left, mul_zero, Real.exp_zero, mul_one]
    exact hM_bound 0 hx y
  rcases eq_or_lt_of_le hx.2 with rfl | hx_lt
  · rw [harmonicMajorantRe_pi_left, mul_zero, Real.exp_zero, mul_one]
    exact hM_bound π hx y
  have hx_open : x ∈ Ioo 0 π := ⟨hx_pos, hx_lt⟩
  have h_eta : ∀ η > 0,
      ‖f ((x : ℂ) + (y : ℂ) * I)‖ * Real.exp (L * harmonicMajorantRe x (y + η)) ≤ M := by
    intro η hη
    have h_ev_Y : ∀ᶠ Y : ℝ in atTop,
        ‖f ((x : ℂ) + (y : ℂ) * I)‖ * Real.exp (L * harmonicMajorantRe x (y + η)) ≤
          M * Real.exp (L * harmonicMajorantRe (π / 2) (Y + η)) := by
      filter_upwards [eventually_gt_atTop y] with Y hY
      exact norm_shiftedMajorantAux_le_on_rect hδ hδM hη (lt_trans hy hY)
        hf_diff hf_cont hM_bound hδ_bound hx_open ⟨hy, hY⟩
    have h_tendsto_Y : Tendsto
        (fun Y : ℝ => M * Real.exp (L * harmonicMajorantRe (π / 2) (Y + η)))
        atTop (𝓝 M) := by
      have h_sinh : Tendsto (fun Y : ℝ => Real.sinh (Y + η)) atTop atTop :=
        tendsto_sinh_atTop.comp (tendsto_id.atTop_add tendsto_const_nhds)
      have h_div : Tendsto (fun Y : ℝ => Real.sin (π / 2) / Real.sinh (Y + η)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop h_sinh
      have h_atan : Tendsto
          (fun Y : ℝ => Real.arctan (Real.sin (π / 2) / Real.sinh (Y + η))) atTop (𝓝 0) := by
        rw [← Real.arctan_zero]
        exact (Real.continuous_arctan.tendsto 0).comp h_div
      have h_om : Tendsto (fun Y : ℝ => harmonicMajorantRe (π / 2) (Y + η)) atTop (𝓝 0) := by
        simpa [harmonicMajorantRe] using h_atan.const_mul (2 / π)
      have h_L_om : Tendsto
          (fun Y : ℝ => L * harmonicMajorantRe (π / 2) (Y + η)) atTop (𝓝 0) := by
        simpa using h_om.const_mul L
      have h_exp : Tendsto
          (fun Y : ℝ => Real.exp (L * harmonicMajorantRe (π / 2) (Y + η))) atTop (𝓝 1) := by
        rw [← Real.exp_zero]
        exact (Real.continuous_exp.tendsto 0).comp h_L_om
      simpa using h_exp.const_mul M
    exact ge_of_tendsto h_tendsto_Y h_ev_Y
  have h_cont_eta : ContinuousAt
      (fun η : ℝ =>
        ‖f ((x : ℂ) + (y : ℂ) * I)‖ * Real.exp (L * harmonicMajorantRe x (y + η)))
      0 := by
    unfold harmonicMajorantRe
    have hsinh_ne : Real.sinh (y + 0) ≠ 0 := by
      rw [add_zero]
      exact (sinh_pos_of_pos hy).ne'
    fun_prop (disch := assumption)
  have h_tendsto_eta : Tendsto
      (fun η : ℝ =>
        ‖f ((x : ℂ) + (y : ℂ) * I)‖ * Real.exp (L * harmonicMajorantRe x (y + η)))
      (𝓝[>] 0)
      (𝓝 (‖f ((x : ℂ) + (y : ℂ) * I)‖ * Real.exp (L * harmonicMajorantRe x y))) := by
    simpa [add_zero] using h_cont_eta.tendsto.mono_left nhdsWithin_le_nhds
  have h_ev_eta : ∀ᶠ η : ℝ in 𝓝[>] 0,
      ‖f ((x : ℂ) + (y : ℂ) * I)‖ * Real.exp (L * harmonicMajorantRe x (y + η)) ≤ M := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact h_eta η hη
  exact le_of_tendsto h_tendsto_eta h_ev_eta

/-- Two-Constants Theorem on the normalized vertical strip $x \in [0, \pi]$, $y \in \mathbb{R}$. -/
theorem norm_le_two_constants_normalized {f : ℂ → ℂ} {M δ : ℝ}
    (hδ : 0 < δ) (hδM : δ ≤ M)
    (hf_diff : DifferentiableOn ℂ f {z : ℂ | z.re ∈ Ioo 0 π})
    (hf_cont : ContinuousOn f {z : ℂ | z.re ∈ Icc 0 π})
    (hM_bound : ∀ x ∈ Icc 0 π, ∀ y : ℝ, ‖f ((x : ℂ) + (y : ℂ) * I)‖ ≤ M)
    (hδ_bound : ∀ x ∈ Icc 0 π, ‖f (x : ℂ)‖ ≤ δ)
    {x : ℝ} (hx : x ∈ Icc 0 π) (y : ℝ) :
    ‖f ((x : ℂ) + (y : ℂ) * I)‖ ≤
      M ^ (1 - stripHarmonicMeasureNormalized x y) *
        δ ^ (stripHarmonicMeasureNormalized x y) := by
  rcases lt_trichotomy y 0 with hy_neg | rfl | hy_pos
  · -- Case y < 0: apply the y > 0 bound to the holomorphic reflection z ↦ f (π - z)
    set f_refl : ℂ → ℂ := fun z => f ((π : ℂ) - z)
    have h_refl_diff : DifferentiableOn ℂ f_refl {z : ℂ | z.re ∈ Ioo 0 π} := by
      refine hf_diff.comp (differentiable_id.const_sub (π : ℂ)).differentiableOn ?_
      intro z hz
      simp only [mem_ofPred_eq, sub_re, ofReal_re, mem_Ioo] at hz ⊢
      exact ⟨by linarith [hz.2], by linarith [hz.1]⟩
    have h_refl_cont : ContinuousOn f_refl {z : ℂ | z.re ∈ Icc 0 π} := by
      refine hf_cont.comp (continuous_const.sub continuous_id).continuousOn ?_
      intro z hz
      simp only [mem_ofPred_eq, sub_re, ofReal_re, mem_Icc] at hz ⊢
      exact ⟨by linarith [hz.2], by linarith [hz.1]⟩
    have h_refl_M :
        ∀ x' ∈ Icc 0 π, ∀ y' : ℝ, ‖f_refl ((x' : ℂ) + (y' : ℂ) * I)‖ ≤ M := by
      intro x' hx' y'
      have h_eq : (π : ℂ) - ((x' : ℂ) + (y' : ℂ) * I) =
          ((π - x' : ℝ) : ℂ) + ((-y' : ℝ) : ℂ) * I := by push_cast; ring
      dsimp [f_refl]
      rw [h_eq]
      exact hM_bound (π - x') ⟨by linarith [hx'.2], by linarith [hx'.1]⟩ (-y')
    have h_refl_δ : ∀ x' ∈ Icc 0 π, ‖f_refl (x' : ℂ)‖ ≤ δ := by
      intro x' hx'
      have h_eq : (π : ℂ) - (x' : ℂ) = ((π - x' : ℝ) : ℂ) := by push_cast; ring
      dsimp [f_refl]
      rw [h_eq]
      exact hδ_bound (π - x') ⟨by linarith [hx'.2], by linarith [hx'.1]⟩
    have hx' : π - x ∈ Icc 0 π := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hy' : 0 < -y := neg_pos.mpr hy_neg
    have h_bound := norm_le_two_constants_normalized_pos hδ hδM
      h_refl_diff h_refl_cont h_refl_M h_refl_δ hx' hy'
    have h_arg : f_refl (((π - x : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) =
        f ((x : ℂ) + (y : ℂ) * I) := by
      dsimp [f_refl]
      congr 1
      push_cast
      ring
    have h_om : harmonicMajorantRe (π - x) (-y) = stripHarmonicMeasureNormalized x y := by
      rw [← stripHarmonicMeasureNormalized_of_pos hy',
        stripHarmonicMeasureNormalized_pi_sub, stripHarmonicMeasureNormalized_neg]
    rw [h_arg, h_om] at h_bound
    exact h_bound
  · -- Case y = 0:
    have h_om : stripHarmonicMeasureNormalized x 0 = 1 := by
      simp [stripHarmonicMeasureNormalized]
    rw [h_om, sub_self, Real.rpow_zero, Real.rpow_one, one_mul, ofReal_zero, zero_mul, add_zero]
    exact hδ_bound x hx
  · -- Case y > 0:
    rw [stripHarmonicMeasureNormalized_of_pos hy_pos]
    exact norm_le_two_constants_normalized_pos hδ hδM hf_diff hf_cont hM_bound hδ_bound hx hy_pos

/-!
## Part 4: General Vertical Strip $[\sigma_-, \sigma_+]$
-/

/-- Harmonic measure on a general vertical strip $\sigma \in [\sigma_-, \sigma_+]$,
$t \in \mathbb{R}$, of the horizontal segment $[\sigma_-, \sigma_+]$ on the real axis ($t = 0$):
$$\omega(\sigma_-, \sigma_+, \sigma, t) = \begin{cases}
  1 & \text{if } t = 0, \\
  \frac{2}{\pi} \arctan\!\left(
    \frac{\sin(\pi (\sigma - \sigma_-) / (\sigma_+ - \sigma_-))}
         {\sinh(\pi |t| / (\sigma_+ - \sigma_-))}\right) & \text{if } t \ne 0.
\end{cases}$$ -/
noncomputable def stripHarmonicMeasure (σ_minus σ_plus σ t : ℝ) : ℝ :=
  if t = 0 then 1
  else (2 / π) * Real.arctan
    (Real.sin (π * (σ - σ_minus) / (σ_plus - σ_minus)) /
      Real.sinh (π * |t| / (σ_plus - σ_minus)))

lemma stripHarmonicMeasure_eq_normalized {σ_minus σ_plus : ℝ} (hσ : σ_minus < σ_plus)
    (σ t : ℝ) :
    stripHarmonicMeasure σ_minus σ_plus σ t =
      stripHarmonicMeasureNormalized
        (π * (σ - σ_minus) / (σ_plus - σ_minus))
        (π * t / (σ_plus - σ_minus)) := by
  unfold stripHarmonicMeasure stripHarmonicMeasureNormalized
  have h_pos : 0 < π / (σ_plus - σ_minus) := div_pos Real.pi_pos (sub_pos.mpr hσ)
  have h_zero : π * t / (σ_plus - σ_minus) = 0 ↔ t = 0 := by
    rw [div_eq_iff (sub_pos.mpr hσ).ne', zero_mul, mul_eq_zero]
    simp [Real.pi_pos.ne']
  have h_abs : |π * t / (σ_plus - σ_minus)| = π * |t| / (σ_plus - σ_minus) := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (sub_pos.mpr hσ)]
  by_cases ht : t = 0
  · simp [ht]
  · have ht' : π * t / (σ_plus - σ_minus) ≠ 0 := mt h_zero.mp ht
    rw [ite_eq_right_iff.mpr (fun h => absurd h ht),
        ite_eq_right_iff.mpr (fun h => absurd h ht'), h_abs]

lemma normalized_arg_mem_Icc {σ_minus σ_plus σ : ℝ} (hσ : σ_minus < σ_plus)
    (h_mem : σ ∈ Icc σ_minus σ_plus) :
    π * (σ - σ_minus) / (σ_plus - σ_minus) ∈ Icc 0 π := by
  have h_diff : 0 < σ_plus - σ_minus := sub_pos.mpr hσ
  refine ⟨div_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr h_mem.1)) h_diff.le, ?_⟩
  rw [div_le_iff₀ h_diff]
  exact mul_le_mul_of_nonneg_left (by linarith [h_mem.2]) Real.pi_pos.le

theorem stripHarmonicMeasure_nonneg {σ_minus σ_plus σ : ℝ} (hσ : σ_minus < σ_plus)
    (h_mem : σ ∈ Icc σ_minus σ_plus) (t : ℝ) :
    0 ≤ stripHarmonicMeasure σ_minus σ_plus σ t := by
  rw [stripHarmonicMeasure_eq_normalized hσ]
  set x := π * (σ - σ_minus) / (σ_plus - σ_minus)
  set y := π * t / (σ_plus - σ_minus)
  have hx : x ∈ Icc 0 π := normalized_arg_mem_Icc hσ h_mem
  unfold stripHarmonicMeasureNormalized
  split_ifs with hy
  · positivity
  · exact harmonicMajorantRe_nonneg hx (abs_pos.mpr hy)

theorem stripHarmonicMeasure_le_one (σ_minus σ_plus σ t : ℝ) :
    stripHarmonicMeasure σ_minus σ_plus σ t ≤ 1 := by
  unfold stripHarmonicMeasure
  split_ifs
  · exact le_rfl
  · exact harmonicMajorantRe_le_one _ _

theorem stripHarmonicMeasure_anti_abs_t {σ_minus σ_plus σ t₁ t₂ : ℝ}
    (hσ : σ_minus < σ_plus) (h_mem : σ ∈ Icc σ_minus σ_plus)
    (ht : |t₁| ≤ |t₂|) :
    stripHarmonicMeasure σ_minus σ_plus σ t₂ ≤
      stripHarmonicMeasure σ_minus σ_plus σ t₁ := by
  by_cases ht₁ : t₁ = 0
  · subst ht₁
    have h1 : stripHarmonicMeasure σ_minus σ_plus σ 0 = 1 := by simp [stripHarmonicMeasure]
    rw [h1]
    exact stripHarmonicMeasure_le_one σ_minus σ_plus σ t₂
  · have ht₁_abs : 0 < |t₁| := abs_pos.mpr ht₁
    have ht₂_abs : 0 < |t₂| := lt_of_lt_of_le ht₁_abs ht
    have ht₂ : t₂ ≠ 0 := abs_pos.mp ht₂_abs
    unfold stripHarmonicMeasure
    rw [ite_eq_right_iff.mpr (fun h => absurd h ht₂),
        ite_eq_right_iff.mpr (fun h => absurd h ht₁)]
    have h_diff : 0 < σ_plus - σ_minus := sub_pos.mpr hσ
    have hy₁ : 0 < π * |t₁| / (σ_plus - σ_minus) := by positivity
    have hy_le : π * |t₁| / (σ_plus - σ_minus) ≤ π * |t₂| / (σ_plus - σ_minus) := by
      gcongr
    exact harmonicMajorantRe_anti_right (normalized_arg_mem_Icc hσ h_mem) hy₁ hy_le

/-- **Nevanlinna's Two-Constants Theorem on a Vertical Strip**:
If $E : \mathbb{C} \to \mathbb{C}$ is differentiable on the open strip
$\{\operatorname{Re} s \in (\sigma_-, \sigma_+)\}$, continuous on the closed strip
$\{\operatorname{Re} s \in [\sigma_-, \sigma_+]\}$, bounded by $M$ on the closed strip, and bounded
by $\delta \in (0, M]$ on the real segment $[\sigma_-, \sigma_+]$, then for all
$\sigma \in [\sigma_-, \sigma_+]$ and $t \in \mathbb{R}$,
$$\|E(\sigma + it)\| \le M^{1 - \omega(\sigma, t)} \, \delta^{\omega(\sigma, t)}.$$ -/
theorem norm_le_two_constants_vertical_strip {E : ℂ → ℂ} {σ_minus σ_plus M δ : ℝ}
    (hσ : σ_minus < σ_plus) (hδ : 0 < δ) (hδM : δ ≤ M)
    (hE_diff : DifferentiableOn ℂ E {s : ℂ | s.re ∈ Ioo σ_minus σ_plus})
    (hE_cont : ContinuousOn E {s : ℂ | s.re ∈ Icc σ_minus σ_plus})
    (hM_bound :
      ∀ σ ∈ Icc σ_minus σ_plus, ∀ t : ℝ, ‖E ((σ : ℂ) + (t : ℂ) * I)‖ ≤ M)
    (hδ_bound : ∀ σ ∈ Icc σ_minus σ_plus, ‖E (σ : ℂ)‖ ≤ δ)
    {σ : ℝ} (h_mem : σ ∈ Icc σ_minus σ_plus) (t : ℝ) :
    ‖E ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      M ^ (1 - stripHarmonicMeasure σ_minus σ_plus σ t) *
        δ ^ (stripHarmonicMeasure σ_minus σ_plus σ t) := by
  have h_diff_pos : 0 < σ_plus - σ_minus := sub_pos.mpr hσ
  set c : ℝ := (σ_plus - σ_minus) / π
  have hc_pos : 0 < c := div_pos h_diff_pos Real.pi_pos
  set φ : ℂ → ℂ := fun z => (σ_minus : ℂ) + (c : ℂ) * z
  set f : ℂ → ℂ := fun z => E (φ z)
  have hφ_re : ∀ z : ℂ, (φ z).re = σ_minus + c * z.re := by
    intro z
    simp [φ, add_re, mul_re]
  have hc_pi : c * π = σ_plus - σ_minus := div_mul_cancel₀ _ Real.pi_pos.ne'
  have hf_diff : DifferentiableOn ℂ f {z : ℂ | z.re ∈ Ioo 0 π} := by
    refine hE_diff.comp ((differentiable_id.const_mul (c : ℂ)).const_add _).differentiableOn ?_
    intro z hz
    simp only [mem_ofPred_eq, hφ_re, mem_Ioo] at hz ⊢
    refine ⟨?_, ?_⟩
    · have : 0 < c * z.re := mul_pos hc_pos hz.1
      linarith
    · have : c * z.re < c * π := mul_lt_mul_of_pos_left hz.2 hc_pos
      linarith
  have hf_cont : ContinuousOn f {z : ℂ | z.re ∈ Icc 0 π} := by
    refine hE_cont.comp (continuous_const.add (continuous_const.mul continuous_id)).continuousOn ?_
    intro z hz
    simp only [mem_ofPred_eq, hφ_re, mem_Icc] at hz ⊢
    refine ⟨?_, ?_⟩
    · have : 0 ≤ c * z.re := mul_nonneg hc_pos.le hz.1
      linarith
    · have : c * z.re ≤ c * π := mul_le_mul_of_nonneg_left hz.2 hc_pos.le
      linarith
  have hf_M : ∀ x ∈ Icc 0 π, ∀ y : ℝ, ‖f ((x : ℂ) + (y : ℂ) * I)‖ ≤ M := by
    intro x hx y
    have h_eq : φ ((x : ℂ) + (y : ℂ) * I) =
        ((σ_minus + c * x : ℝ) : ℂ) + ((c * y : ℝ) : ℂ) * I := by
      dsimp [φ]; push_cast; ring
    dsimp [f]
    rw [h_eq]
    refine hM_bound (σ_minus + c * x) ⟨?_, ?_⟩ (c * y)
    · have : 0 ≤ c * x := mul_nonneg hc_pos.le hx.1
      linarith
    · have : c * x ≤ c * π := mul_le_mul_of_nonneg_left hx.2 hc_pos.le
      linarith
  have hf_δ : ∀ x ∈ Icc 0 π, ‖f (x : ℂ)‖ ≤ δ := by
    intro x hx
    have h_eq : φ (x : ℂ) = ((σ_minus + c * x : ℝ) : ℂ) := by
      dsimp [φ]; push_cast; ring
    dsimp [f]
    rw [h_eq]
    refine hδ_bound (σ_minus + c * x) ⟨?_, ?_⟩
    · have : 0 ≤ c * x := mul_nonneg hc_pos.le hx.1
      linarith
    · have : c * x ≤ c * π := mul_le_mul_of_nonneg_left hx.2 hc_pos.le
      linarith
  set x := π * (σ - σ_minus) / (σ_plus - σ_minus)
  set y := π * t / (σ_plus - σ_minus)
  have hx : x ∈ Icc 0 π := normalized_arg_mem_Icc hσ h_mem
  have h_norm := norm_le_two_constants_normalized hδ hδM hf_diff hf_cont hf_M hf_δ hx y
  have hcx : σ_minus + c * x = σ := by
    dsimp [c, x]
    have h1 : σ_plus - σ_minus ≠ 0 := h_diff_pos.ne'
    have h2 : π ≠ 0 := Real.pi_pos.ne'
    field_simp
    ring
  have hcy : c * y = t := by
    dsimp [c, y]
    have h1 : σ_plus - σ_minus ≠ 0 := h_diff_pos.ne'
    have h2 : π ≠ 0 := Real.pi_pos.ne'
    field_simp
  have hf_xy : f ((x : ℂ) + (y : ℂ) * I) = E ((σ : ℂ) + (t : ℂ) * I) := by
    dsimp [f, φ]
    congr 1
    rw [← hcx, ← hcy]
    push_cast
    ring
  rw [hf_xy, ← stripHarmonicMeasure_eq_normalized hσ σ t] at h_norm
  exact h_norm

/-!
## Part 5: Midpoint Harmonic Measure Exponent on $[1 - 2A, -1]$
-/

/-- The harmonic measure exponent at the midpoint $\sigma = -A$ of the vertical strip
$[1 - 2A, -1]$ at height $T > 0$:
$$\theta(A, T) = \frac{2}{\pi} \arctan\!\left(\frac{1}{\sinh(\pi T / (2 (A - 1)))}\right).$$ -/
noncomputable def midpointHarmonicExp (A T : ℝ) : ℝ :=
  (2 / π) * Real.arctan (1 / Real.sinh (π * T / (2 * (A - 1))))

theorem midpointHarmonicExp_pos {A T : ℝ} (hA : 1 < A) (hT : 0 < T) :
    0 < midpointHarmonicExp A T := by
  unfold midpointHarmonicExp
  have h_arg : 0 < π * T / (2 * (A - 1)) := by
    have : 0 < A - 1 := sub_pos.mpr hA
    positivity
  have h_sinh : 0 < Real.sinh (π * T / (2 * (A - 1))) := sinh_pos_of_pos h_arg
  have h_atan : 0 < Real.arctan (1 / Real.sinh (π * T / (2 * (A - 1)))) :=
    Real.arctan_pos.mpr (by positivity)
  positivity

theorem midpointHarmonicExp_lt_one (A T : ℝ) :
    midpointHarmonicExp A T < 1 := by
  unfold midpointHarmonicExp
  have h_lt : Real.arctan (1 / Real.sinh (π * T / (2 * (A - 1)))) < π / 2 :=
    Real.arctan_lt_pi_div_two _
  have hpi : 0 < π := Real.pi_pos
  calc (2 / π) * Real.arctan (1 / Real.sinh (π * T / (2 * (A - 1))))
      < (2 / π) * (π / 2) := mul_lt_mul_of_pos_left h_lt (by positivity)
    _ = 1 := by field_simp

theorem stripHarmonicMeasure_midpoint {A T : ℝ} (hA : 1 < A) (hT : 0 < T) :
    stripHarmonicMeasure (1 - 2 * A) (-1) (-A) T = midpointHarmonicExp A T := by
  unfold stripHarmonicMeasure midpointHarmonicExp
  rw [ite_eq_right_iff.mpr (fun h => absurd h hT.ne'), abs_of_pos hT]
  congr 3
  · have h_arg : π * (-A - (1 - 2 * A)) / (-1 - (1 - 2 * A)) = π / 2 := by
      have hA_ne : A - 1 ≠ 0 := (sub_pos.mpr hA).ne'
      have h1 : -A - (1 - 2 * A) = A - 1 := by ring
      have h2 : -1 - (1 - 2 * A) = 2 * (A - 1) := by ring
      rw [h1, h2]
      field_simp
    rw [h_arg, Real.sin_pi_div_two]
  · congr 1
    have h2 : -1 - (1 - 2 * A) = 2 * (A - 1) := by ring
    rw [h2]

/-- As the strip half-width $A - 1 \to +\infty$, the midpoint harmonic measure exponent
$\theta(A, T) \to 1$. -/
theorem tendsto_midpointHarmonicExp_atTop {T : ℝ} (hT : 0 < T) :
    Tendsto (fun A : ℝ => midpointHarmonicExp A T) atTop (𝓝 1) := by
  unfold midpointHarmonicExp
  have h_lin : Tendsto (fun A : ℝ => 2 * (A - 1)) atTop atTop :=
    (tendsto_id.atTop_add tendsto_const_nhds).const_mul_atTop (by positivity)
  have h_arg_zero : Tendsto (fun A : ℝ => π * T / (2 * (A - 1))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h_lin
  have h_arg_pos : ∀ᶠ A : ℝ in atTop, 0 < π * T / (2 * (A - 1)) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with A hA
    have : 0 < A - 1 := sub_pos.mpr hA
    positivity
  have h_sinh_zero : Tendsto
      (fun A : ℝ => Real.sinh (π * T / (2 * (A - 1)))) atTop (𝓝 0) := by
    rw [← Real.sinh_zero]
    exact (Real.continuous_sinh.tendsto 0).comp h_arg_zero
  have h_sinh_pos : ∀ᶠ A : ℝ in atTop, 0 < Real.sinh (π * T / (2 * (A - 1))) := by
    filter_upwards [h_arg_pos] with A hA
    exact sinh_pos_of_pos hA
  have h_sinh_nhds : Tendsto
      (fun A : ℝ => Real.sinh (π * T / (2 * (A - 1)))) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨h_sinh_zero, h_sinh_pos⟩
  have h_inv_atTop : Tendsto
      (fun A : ℝ => 1 / Real.sinh (π * T / (2 * (A - 1)))) atTop atTop := by
    have h_inv := tendsto_inv_nhdsGT_zero.comp h_sinh_nhds
    exact h_inv.congr (fun A => (one_div _).symm)
  have h_atan : Tendsto
      (fun A : ℝ => Real.arctan (1 / Real.sinh (π * T / (2 * (A - 1)))))
      atTop (𝓝 (π / 2)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp h_inv_atTop
  have h_prod : Tendsto
      (fun A : ℝ => (2 / π) * Real.arctan (1 / Real.sinh (π * T / (2 * (A - 1)))))
      atTop (𝓝 ((2 / π) * (π / 2))) :=
    h_atan.const_mul (2 / π)
  have h_one : (2 / π) * (π / 2) = 1 := by
    have hpi : π ≠ 0 := Real.pi_pos.ne'
    field_simp
  rwa [h_one] at h_prod

/-- **Midpoint Two-Constants Corollary on $[1 - 2A, -1]$**:
For $A > 1$, $T > 0$, and $0 < \delta \le M$, if $E : \mathbb{C} \to \mathbb{C}$ is holomorphic
on the open strip $\{\operatorname{Re} s \in (1 - 2A, -1)\}$, continuous on the closed strip
$\{\operatorname{Re} s \in [1 - 2A, -1]\}$, bounded by $M$ on the closed strip, and bounded by
$\delta$ on the real interval $[1 - 2A, -1]$, then for all $t \in [-T, T]$:
$$\|E(-A + it)\| \le M^{1 - \theta(A, T)} \, \delta^{\theta(A, T)}.$$ -/
theorem norm_le_midpoint_two_constants {E : ℂ → ℂ} {A T M δ : ℝ}
    (hA : 1 < A) (hT : 0 < T) (hδ : 0 < δ) (hδM : δ ≤ M)
    (hE_diff : DifferentiableOn ℂ E {s : ℂ | s.re ∈ Ioo (1 - 2 * A) (-1)})
    (hE_cont : ContinuousOn E {s : ℂ | s.re ∈ Icc (1 - 2 * A) (-1)})
    (hM_bound :
      ∀ σ ∈ Icc (1 - 2 * A) (-1), ∀ t : ℝ, ‖E ((σ : ℂ) + (t : ℂ) * I)‖ ≤ M)
    (hδ_bound : ∀ σ ∈ Icc (1 - 2 * A) (-1), ‖E (σ : ℂ)‖ ≤ δ)
    {t : ℝ} (ht : t ∈ Icc (-T) T) :
    ‖E ((-A : ℂ) + (t : ℂ) * I)‖ ≤
      M ^ (1 - midpointHarmonicExp A T) * δ ^ (midpointHarmonicExp A T) := by
  have hσ : 1 - 2 * A < -1 := by linarith
  have h_mid : -A ∈ Icc (1 - 2 * A) (-1) := ⟨by linarith, by linarith⟩
  have h_strip := norm_le_two_constants_vertical_strip hσ hδ hδM
    hE_diff hE_cont hM_bound hδ_bound h_mid t
  push_cast at h_strip
  have ht_abs : |t| ≤ |T| := by
    rw [abs_of_pos hT]
    exact abs_le.mpr ht
  have h_om_le : midpointHarmonicExp A T ≤ stripHarmonicMeasure (1 - 2 * A) (-1) (-A) t := by
    rw [← stripHarmonicMeasure_midpoint hA hT]
    exact stripHarmonicMeasure_anti_abs_t hσ h_mid ht_abs
  set ω_t := stripHarmonicMeasure (1 - 2 * A) (-1) (-A) t
  set ω_T := midpointHarmonicExp A T
  have hM_pos : 0 < M := lt_of_lt_of_le hδ hδM
  have h_rpow_le : M ^ (1 - ω_t) * δ ^ ω_t ≤ M ^ (1 - ω_T) * δ ^ ω_T := by
    rw [Real.rpow_def_of_pos hM_pos, Real.rpow_def_of_pos hδ, ← Real.exp_add,
        Real.rpow_def_of_pos hM_pos, Real.rpow_def_of_pos hδ, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h_log : Real.log δ ≤ Real.log M := Real.log_le_log hδ hδM
    nlinarith
  exact h_strip.trans h_rpow_le
