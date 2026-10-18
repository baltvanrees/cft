/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Balt van Rees
-/
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Positivity

/-!
# One-Dimensional ($SL(2, \mathbb{R})$ / Collinear) Conformal Blocks

This file defines the one-dimensional (collinear) conformal blocks $k_h(e^w)$ of conformal weight
$h$ in the universal-cover coordinate $w$ (where $\rho = e^w$ and $\operatorname{Re}(w) < 0$):
$$
k_h(e^w) = e^{h w} \, {}_2F_1\!\left(h, \frac{1}{2}; h + \frac{1}{2}; e^{2w}\right)
  = \sum_{n=0}^{\infty} \frac{(h)_n (1/2)_n}{(h + 1/2)_n \, n!} e^{(h + 2n) w}.
$$
For $h \ge 0$, all series coefficients are non-negative and bounded above by $1$, ensuring absolute
convergence on the left half-plane $\operatorname{Re}(w) < 0$.
-/

open Real Complex Topology Set Metric Polynomial

/-- Rising Pochhammer symbol $(x)_n$ evaluated on `ℝ`. -/
noncomputable def realPochhammer (x : ℝ) (n : ℕ) : ℝ :=
  (ascPochhammer ℝ n).eval x

@[simp]
lemma realPochhammer_zero (x : ℝ) : realPochhammer x 0 = 1 := by
  simp [realPochhammer]

lemma realPochhammer_succ (x : ℝ) (n : ℕ) :
    realPochhammer x (n + 1) = realPochhammer x n * (x + (n : ℝ)) := by
  simp [realPochhammer, ascPochhammer_succ_eval]

lemma realPochhammer_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    0 ≤ realPochhammer x n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [realPochhammer_succ]
    positivity

lemma realPochhammer_pos {x : ℝ} (hx : 0 < x) (n : ℕ) :
    0 < realPochhammer x n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [realPochhammer_succ]
    positivity

lemma realPochhammer_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (n : ℕ) :
    realPochhammer x n ≤ realPochhammer y n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [realPochhammer_succ, realPochhammer_succ]
    refine mul_le_mul ih (by linarith) ?_ (realPochhammer_nonneg (by linarith) k)
    positivity

lemma realPochhammer_one (n : ℕ) :
    realPochhammer 1 n = (n.factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [realPochhammer_succ, ih, Nat.factorial_succ]
    push_cast
    ring

/-- Expansion coefficient of $e^{(h + 2n) w}$ in the 1D conformal block
$k_h(e^w) = e^{h w} \, {}_2F_1(h, 1/2; h + 1/2; e^{2w})$:
$$c_n(h) = \frac{(h)_n (1/2)_n}{(h + 1/2)_n \, n!}.$$ -/
noncomputable def block1dCoeff (h : ℝ) (n : ℕ) : ℝ :=
  realPochhammer h n * realPochhammer (1 / 2) n /
    (realPochhammer (h + 1 / 2) n * (n.factorial : ℝ))

@[simp]
lemma block1dCoeff_zero (h : ℝ) : block1dCoeff h 0 = 1 := by
  simp [block1dCoeff]

lemma block1dCoeff_nonneg {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    0 ≤ block1dCoeff h n := by
  dsimp [block1dCoeff]
  have h1 : 0 ≤ realPochhammer h n := realPochhammer_nonneg hh n
  have h2 : 0 < realPochhammer (1 / 2) n := realPochhammer_pos (by norm_num) n
  have h3 : 0 < realPochhammer (h + 1 / 2) n := realPochhammer_pos (by linarith) n
  have h4 : (0 : ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
  positivity

lemma block1dCoeff_pos {h : ℝ} (hh : 0 < h) (n : ℕ) :
    0 < block1dCoeff h n := by
  dsimp [block1dCoeff]
  have h1 : 0 < realPochhammer h n := realPochhammer_pos hh n
  have h2 : 0 < realPochhammer (1 / 2) n := realPochhammer_pos (by norm_num) n
  have h3 : 0 < realPochhammer (h + 1 / 2) n := realPochhammer_pos (by linarith) n
  have h4 : (0 : ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
  positivity

lemma block1dCoeff_le_one {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    block1dCoeff h n ≤ 1 := by
  dsimp [block1dCoeff]
  have h3 : 0 < realPochhammer (h + 1 / 2) n := realPochhammer_pos (by linarith) n
  have h4 : (0 : ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
  rw [div_le_one (mul_pos h3 h4)]
  have h_le1 : realPochhammer h n ≤ realPochhammer (h + 1 / 2) n :=
    realPochhammer_mono hh (by linarith) n
  have h_le2 : realPochhammer (1 / 2) n ≤ (n.factorial : ℝ) := by
    rw [← realPochhammer_one]
    exact realPochhammer_mono (by norm_num) (by norm_num) n
  exact mul_le_mul h_le1 h_le2
    (realPochhammer_nonneg (by norm_num) n) (le_of_lt h3)

/-- The one-dimensional ($SL(2, \mathbb{R})$ / collinear) conformal block of weight $h$ in the
coordinate $w$ (where $\rho = e^w$ and $\operatorname{Re}(w) < 0$):
$$k_h(e^w) = e^{h w} \, {}_2F_1\!\left(h, \frac{1}{2}; h + \frac{1}{2}; e^{2w}\right)
  = \sum_{n=0}^{\infty} \frac{(h)_n (1/2)_n}{(h + 1/2)_n \, n!} e^{(h + 2n) w}.$$ -/
noncomputable def block1d (h : ℝ) (w : ℂ) : ℂ :=
  ∑' n : ℕ, (block1dCoeff h n : ℂ) * Complex.exp (((h + 2 * (n : ℝ) : ℝ) : ℂ) * w)

lemma summable_block1d {h : ℝ} (hh : 0 ≤ h) {w : ℂ} (hw : w.re < 0) :
    Summable (fun n : ℕ =>
      (block1dCoeff h n : ℂ) * Complex.exp (((h + 2 * (n : ℝ) : ℝ) : ℂ) * w)) := by
  have h_geom : Summable (fun n : ℕ => Real.exp (h * w.re) * (Real.exp (2 * w.re)) ^ n) := by
    apply Summable.mul_left
    apply summable_geometric_of_lt_one (Real.exp_nonneg _)
    rw [Real.exp_lt_one_iff]
    linarith
  refine Summable.of_norm_bounded h_geom (fun n => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (block1dCoeff_nonneg hh n),
    Complex.norm_exp, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
    add_mul, Real.exp_add]
  have h_pow : Real.exp (2 * (n : ℝ) * w.re) = (Real.exp (2 * w.re)) ^ n := by
    rw [← Real.exp_nat_mul]
    ring_nf
  rw [h_pow]
  exact mul_le_of_le_one_left (by positivity) (block1dCoeff_le_one hh n)
