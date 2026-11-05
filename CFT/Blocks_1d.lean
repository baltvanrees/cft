/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI-generated, edited by Balt van Rees
-/
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Positivity

/-!
# One-Dimensional Conformal Blocks

This file defines the one-dimensional (collinear or $SL(2,ℝ)$) conformal blocks $k_h(e^w)$ of
conformal weight $h$, using a coordinate $w$ such that $\rho = e^w$. This allows for a smooth
extension to the universal cover of the polydisk, which is the domain $\operatorname{Re}(w) < 0$).

We have:
$$
k_h(e^w) = e^{h w} \, {}_2F_1\!\left(h, \frac{1}{2}; h + \frac{1}{2}; e^{2w}\right)
  = \sum_{n=0}^{\infty} \frac{(h)_n (1/2)_n}{(h + 1/2)_n \, n!} e^{(h + 2n) w}.
$$
For $h \ge 0$, all series coefficients are non-negative and bounded above by $1$, ensuring absolute
convergence on the left half-plane.
-/

open Real Complex Topology Set Metric Polynomial

/-- Real rising Pochhammer symbol $(x)_n$. -/
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

/-- Coefficient of $e^{(h + 2n) w}$ in the expansion of the conformal block:
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

/-- The one-dimensional conformal block defined through its series expansion as above. -/
noncomputable def block1d (h : ℝ) (w : ℂ) : ℂ :=
  ∑' n : ℕ, (block1dCoeff h n : ℂ) * Complex.exp (((h + 2 * (n : ℝ) : ℝ) : ℂ) * w)

/-- Proof of summability (convergence) of the sum if $\operatorname{Re}(w) < 0$ and $0 ≤ h$. -/
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

/-!
## 1D Generalized Free Field (GFF) Conformal Block Expansion

The 1D $t$-channel identity crossing factor
$$
4^{\Delta_\phi} e^{\Delta_\phi w} (1 - e^w)^{-2\Delta_\phi}
$$
decomposes on the left half-plane $\operatorname{Re}(w) < 0$ into a non-negative series of 1D
conformal blocks $k_{\Delta_\phi + m}(e^w)$ with explicit hypergeometric coefficients
`gffBlockCoeff Δ_phi m`.
-/

/-- The 1D GFF collinear block coefficients $c_m(\Delta_\phi)$ in the expansion of the $t$-channel
identity factor into 1D conformal blocks $k_{\Delta_\phi + m}(e^w)$. -/
noncomputable def gffBlockCoeff (Δ_phi : ℝ) : ℕ → ℝ
  | 0 => (4 : ℝ) ^ (2 * Δ_phi) / (4 * Real.sqrt π)
  | m + 1 =>
      ((4 : ℝ) ^ (2 * Δ_phi) / (4 * Real.sqrt π)) *
        (4 : ℝ) ^ (m + 1) * (realPochhammer Δ_phi (m + 1)) ^ 2 /
          (((m + 1).factorial : ℝ) * realPochhammer (2 * Δ_phi + (m : ℝ)) (m + 1))

@[simp]
lemma gffBlockCoeff_zero (Δ_phi : ℝ) :
    gffBlockCoeff Δ_phi 0 = (4 : ℝ) ^ (2 * Δ_phi) / (4 * Real.sqrt π) :=
  rfl

@[simp]
lemma gffBlockCoeff_succ (Δ_phi : ℝ) (m : ℕ) :
    gffBlockCoeff Δ_phi (m + 1) =
      ((4 : ℝ) ^ (2 * Δ_phi) / (4 * Real.sqrt π)) *
        (4 : ℝ) ^ (m + 1) * (realPochhammer Δ_phi (m + 1)) ^ 2 /
          (((m + 1).factorial : ℝ) * realPochhammer (2 * Δ_phi + (m : ℝ)) (m + 1)) :=
  rfl

/-- Strict positivity of `gffBlockCoeff Δ_phi m` for all $\Delta_\phi > 0$ and
$m \in \mathbb{N}$. -/
theorem gffBlockCoeff_pos {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) (m : ℕ) :
    0 < gffBlockCoeff Δ_phi m := by
  cases m with
  | zero =>
    rw [gffBlockCoeff_zero]
    positivity
  | succ k =>
    rw [gffBlockCoeff_succ]
    have h1 : 0 < realPochhammer Δ_phi (k + 1) := realPochhammer_pos hΔ (k + 1)
    have h2 : 0 < realPochhammer (2 * Δ_phi + (k : ℝ)) (k + 1) :=
      realPochhammer_pos (by positivity) (k + 1)
    have h3 : (0 : ℝ) < ((k + 1).factorial : ℝ) :=
      Nat.cast_pos.mpr (Nat.factorial_pos (k + 1))
    positivity

lemma gffBlockCoeff_nonneg {Δ_phi : ℝ} (hΔ : 0 < Δ_phi) (m : ℕ) :
    0 ≤ gffBlockCoeff Δ_phi m :=
  (gffBlockCoeff_pos hΔ m).le

/-- The 1D GFF collinear block series
$$
\operatorname{gffBlockSeries}(\Delta_\phi, z) :=
  \sum_{m=0}^{\infty} c_m(\Delta_\phi) \, \operatorname{block1d}(\Delta_\phi + m, z).
$$ -/
noncomputable def gffBlockSeries (Δ_phi : ℝ) (z : ℂ) : ℂ :=
  ∑' m : ℕ, (gffBlockCoeff Δ_phi m : ℂ) * block1d (Δ_phi + (m : ℝ)) z

/-- 1D GFF conformal block decomposition of the $t$-channel identity crossing factor on the left
half-plane $\operatorname{Re}(w) < 0$:
$$
4^{\Delta_\phi} e^{\Delta_\phi w} (1 - e^w)^{-2\Delta_\phi} =
  \sum_{m=0}^{\infty} c_m(\Delta_\phi) \, k_{\Delta_\phi + m}(e^w).
$$ -/
theorem gffBlockSeries_eq_crossFactor {Δ_phi : ℝ} (_hΔ : 0 < Δ_phi) {w : ℂ} (_hw : w.re < 0) :
    (4 : ℂ) ^ (Δ_phi : ℂ) * Complex.exp ((Δ_phi : ℂ) * w) *
      (1 - Complex.exp w) ^ (- (2 * Δ_phi : ℂ)) =
    gffBlockSeries Δ_phi w := by
  sorry
