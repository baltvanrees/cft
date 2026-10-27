/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Balt van Rees
-/
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import CFT.Blocks_1d
import CFT.LightconeBootstrap.RealLaplaceBound

/-!
# 1D Fractional Transmutation of Collinear Conformal Blocks on `UcDisk`

This file formalizes Phase 1 of the $d$-dimensional primary lightcone bootstrap
(`PLAN_CONFORMAL_BLOCKS.md`): the 1D fractional transmutation operator that collapses any
collinear conformal block `block1d H w` ($H > 1/2$) on `UcDisk` into a single exponential
monomial `exp (H * w)`.

## Main Definitions and Results

1. **Half-Binomial Coefficients & Algebraic Identities (`halfBinom`,
   `sum_halfBinom_mul_halfBinom`, `sum_halfBinom_div_add_eq_pochhammer_div`)**:
   - `halfBinom k = (1/2)_k / k!`: coefficient of $z^k$ in $(1 - z)^{-1/2}$.
   - `sum_halfBinom_mul_halfBinom`: the convolution identity $\sum_{k=0}^m b_k b_{m - k} = 1$.
   - `sum_halfBinom_div_add_eq_pochhammer_div`: the partial-fraction identity
     $$\sum_{k=0}^m \frac{b_k b_{m - k}}{X + k} = \frac{(X + 1/2)_m}{(X)_{m + 1}}.$$

2. **Exact Cancellation of Higher Descendant Modes (`block1dCoeff_mul_pochhammer_div_succ`,
   `sum_transmuteCoeff_eq`)**:
   - Using `sum_halfBinom_div_add_eq_pochhammer_div` and `Finset.sum_comm`, we prove that for
     all $H > 1/2$ and $m \ge 1$, the transmuted descendant mode sums satisfy the exact
     telescoping identity `sum_transmuteCoeff_eq`, so all $m \ge 1$ descendant contributions cancel
     identically.

3. **Transmutation Kernel, Beta Integral, and Action on `block1d` (`transmuteKernel`,
   `transmuteCore`, `transmuteCore_block1d`)**:
   - For $H > 1/2$ and $w \in \operatorname{UcDisk}$,
     $$\operatorname{transmuteCore}(\operatorname{block1d} H)\, w
       = \frac{\Gamma(H - 1/2)}{\Gamma(H)} e^{H w}.$$

4. **$H$-Independent Differential-Integral Operator `transmuteOp` ($\mathcal{L}_0$) and
   Non-Negative Truncated Weight (`derivHalfSub`, `transmuteOp`, `transmuteOp_block1d`,
   `transmutePosWeight`)**:
   - Combining `transmuteCore` with $\bigl(\partial_w - \tfrac{1}{2}\bigr)^2$ (`derivHalfSub`)
     defines the $H$-independent operator
     $$\operatorname{transmuteOp}(f)(w) :=
       \left(\partial_w - \frac{1}{2}\right)^2 \bigl(\operatorname{transmuteCore} f\bigr)(w),$$
     which satisfies `transmuteOp (block1d H) w = transmuteWeight H * exp (H * w)` on `UcDisk`
     and acts linearly on finite sums of 1D conformal blocks (`transmuteOp_finset_sum_block1d`).
   - We also define the non-negative measurable truncation `transmutePosWeight` for weighting CFT
     spectral measures via `Measure.withDensity`.
-/

open Real Complex Topology Set Metric MeasureTheory Filter
open scoped ComplexConjugate

namespace CFT.LightconeBootstrap

/-!
## 1. Half-Binomial Coefficients and the Partial-Fraction Identity
-/

/-- The half-binomial coefficient $b_k = \frac{(1/2)_k}{k!}$, i.e., the coefficient of $z^k$ in
$(1 - z)^{-1/2}$. -/
noncomputable def halfBinom (k : ℕ) : ℝ :=
  realPochhammer (1 / 2) k / (k.factorial : ℝ)

lemma halfBinom_eq_pochhammerCoeff (k : ℕ) :
    halfBinom k = pochhammerCoeff (1 / 2) k := rfl

@[simp]
lemma halfBinom_zero : halfBinom 0 = 1 := by
  simp [halfBinom]

lemma halfBinom_pos (k : ℕ) : 0 < halfBinom k := by
  dsimp [halfBinom]
  exact div_pos (realPochhammer_pos (by norm_num) k) (Nat.cast_pos.mpr (Nat.factorial_pos k))

lemma halfBinom_nonneg (k : ℕ) : 0 ≤ halfBinom k :=
  (halfBinom_pos k).le

lemma halfBinom_le_one (k : ℕ) : halfBinom k ≤ 1 := by
  dsimp [halfBinom]
  have hfact_pos : (0 : ℝ) < (k.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
  rw [div_le_one hfact_pos, ← realPochhammer_one]
  exact realPochhammer_mono (by norm_num) (by norm_num) k

/-- First-order recurrence for `halfBinom`: $(k + 1) b_{k + 1} = (k + 1/2) b_k$. -/
lemma mul_halfBinom_succ (k : ℕ) :
    ((k : ℝ) + 1) * halfBinom (k + 1) = ((k : ℝ) + 1 / 2) * halfBinom k := by
  dsimp [halfBinom]
  rw [realPochhammer_succ, Nat.factorial_succ]
  push_cast
  have hfact : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- Convolution identity for `halfBinom`: $\sum_{k=0}^m b_k b_{m - k} = 1$ for all
$m \in \mathbb{N}$ (reflecting $(1 - z)^{-1/2} (1 - z)^{-1/2} = (1 - z)^{-1}$). -/
theorem sum_halfBinom_mul_halfBinom (m : ℕ) :
    (∑ k ∈ Finset.range (m + 1), halfBinom k * halfBinom (m - k)) = 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hm1_ne : (m : ℝ) + 1 ≠ 0 := by positivity
    apply mul_left_cancel₀ hm1_ne
    rw [mul_one, Finset.mul_sum]
    have h_split :
        (∑ x ∈ Finset.range (m + 1 + 1),
          ((m : ℝ) + 1) * (halfBinom x * halfBinom (m + 1 - x))) =
        (∑ x ∈ Finset.range (m + 1 + 1),
          ((x : ℝ) * halfBinom x) * halfBinom (m + 1 - x)) +
        (∑ x ∈ Finset.range (m + 1 + 1),
          halfBinom x * (((m + 1 - x : ℕ) : ℝ) * halfBinom (m + 1 - x))) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hx_le : x ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
      have h_sub : ((m + 1 - x : ℕ) : ℝ) = (m : ℝ) + 1 - (x : ℝ) := by
        rw [Nat.cast_sub hx_le]
        push_cast
        ring
      rw [h_sub]
      ring
    rw [h_split]
    have h_sum1 :
        (∑ x ∈ Finset.range (m + 1 + 1),
          ((x : ℝ) * halfBinom x) * halfBinom (m + 1 - x)) =
        ∑ j ∈ Finset.range (m + 1),
          (((j : ℝ) + 1 / 2) * halfBinom j) * halfBinom (m - j) := by
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, zero_mul, add_zero, Nat.succ_sub_succ_eq_sub]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Nat.cast_add, Nat.cast_one, mul_halfBinom_succ j]
    have h_sum2 :
        (∑ x ∈ Finset.range (m + 1 + 1),
          halfBinom x * (((m + 1 - x : ℕ) : ℝ) * halfBinom (m + 1 - x))) =
        ∑ j ∈ Finset.range (m + 1),
          halfBinom j * ((((m - j : ℕ) : ℝ) + 1 / 2) * halfBinom (m - j)) := by
      rw [Finset.sum_range_succ]
      simp only [Nat.sub_self, Nat.cast_zero, zero_mul, mul_zero, add_zero]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj_le : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have h_sub_succ : m + 1 - j = (m - j) + 1 := Nat.succ_sub hj_le
      rw [h_sub_succ, Nat.cast_add, Nat.cast_one, mul_halfBinom_succ (m - j)]
    rw [h_sum1, h_sum2, ← Finset.sum_add_distrib]
    have h_comb :
        (∑ j ∈ Finset.range (m + 1),
          ((((j : ℝ) + 1 / 2) * halfBinom j) * halfBinom (m - j) +
            halfBinom j * ((((m - j : ℕ) : ℝ) + 1 / 2) * halfBinom (m - j)))) =
        ((m : ℝ) + 1) * ∑ j ∈ Finset.range (m + 1), halfBinom j * halfBinom (m - j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj_le : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have h_sub : ((m - j : ℕ) : ℝ) = (m : ℝ) - (j : ℝ) := Nat.cast_sub hj_le
      rw [h_sub]
      ring
    rw [h_comb, ih, mul_one]

lemma realPochhammer_ne_zero (n : ℕ) {X : ℝ} (hX : ∀ k < n, X + (k : ℝ) ≠ 0) :
    realPochhammer X n ≠ 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [realPochhammer_succ]
    exact mul_ne_zero (ih fun k hk => hX k (by omega)) (hX n (by omega))

/-- Partial-fraction identity for `halfBinom`: for all $m \in \mathbb{N}$ and $X \in \mathbb{R}$
with $X + k \ne 0$ for $k \le m$,
$$\sum_{k=0}^m \frac{b_k b_{m - k}}{X + k} = \frac{(X + 1/2)_m}{(X)_{m + 1}}.$$ -/
theorem sum_halfBinom_div_add_eq_pochhammer_div (m : ℕ) {X : ℝ}
    (hX : ∀ k ≤ m, X + (k : ℝ) ≠ 0) :
    (∑ k ∈ Finset.range (m + 1), halfBinom k * halfBinom (m - k) / (X + (k : ℝ))) =
      realPochhammer (X + 1 / 2) m / realPochhammer X (m + 1) := by
  induction m with
  | zero =>
    simp [realPochhammer_succ]
  | succ m ih =>
    have hX_m : ∀ k ≤ m, X + (k : ℝ) ≠ 0 := fun k hk => hX k (by omega)
    have hX_succ : X + ((m + 1 : ℕ) : ℝ) ≠ 0 := hX (m + 1) le_rfl
    apply mul_left_cancel₀ hX_succ
    rw [Finset.mul_sum]
    have h_step1 :
        (∑ k ∈ Finset.range (m + 1 + 1),
          (X + ((m + 1 : ℕ) : ℝ)) *
            (halfBinom k * halfBinom (m + 1 - k) / (X + (k : ℝ)))) =
        (∑ k ∈ Finset.range (m + 1 + 1), halfBinom k * halfBinom (m + 1 - k)) +
        (∑ k ∈ Finset.range (m + 1 + 1),
          halfBinom k * (((m + 1 - k : ℕ) : ℝ) * halfBinom (m + 1 - k)) / (X + (k : ℝ))) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk_le : k ≤ m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hk_ne : X + (k : ℝ) ≠ 0 := hX k hk_le
      have h_sub : ((m + 1 - k : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) - (k : ℝ) :=
        Nat.cast_sub hk_le
      rw [h_sub]
      field_simp
      ring
    rw [h_step1, sum_halfBinom_mul_halfBinom (m + 1), Finset.sum_range_succ]
    simp only [Nat.sub_self, Nat.cast_zero, zero_mul, mul_zero, zero_div, add_zero]
    have h_step2 :
        (∑ k ∈ Finset.range (m + 1),
          halfBinom k * (((m + 1 - k : ℕ) : ℝ) * halfBinom (m + 1 - k)) / (X + (k : ℝ))) =
        (X + (m : ℝ) + 1 / 2) *
          (∑ k ∈ Finset.range (m + 1), halfBinom k * halfBinom (m - k) / (X + (k : ℝ))) -
        (∑ k ∈ Finset.range (m + 1), halfBinom k * halfBinom (m - k)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk_le : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hk_ne : X + (k : ℝ) ≠ 0 := hX_m k hk_le
      have h_sub_succ : m + 1 - k = (m - k) + 1 := Nat.succ_sub hk_le
      have h_sub : ((m - k : ℕ) : ℝ) = (m : ℝ) - (k : ℝ) := Nat.cast_sub hk_le
      rw [h_sub_succ, Nat.cast_add, Nat.cast_one, mul_halfBinom_succ (m - k), h_sub]
      field_simp
      ring
    rw [h_step2, sum_halfBinom_mul_halfBinom m, ih hX_m, add_sub_cancel,
      realPochhammer_succ (X + 1 / 2) m, realPochhammer_succ X (m + 1)]
    have h_poch_ne : realPochhammer X (m + 1) ≠ 0 :=
      realPochhammer_ne_zero (m + 1) fun k hk => hX k (by omega)
    have h_cast : X + 1 / 2 + (m : ℝ) = X + (m : ℝ) + 1 / 2 := by ring
    rw [h_cast]
    field_simp

/-!
## 2. Exact Vanishing of Higher Descendant Modes
-/

/-- Addition formula for `realPochhammer`: $(x)_{a + b} = (x)_a (x + a)_b$. -/
lemma realPochhammer_add (x : ℝ) (a b : ℕ) :
    realPochhammer x (a + b) = realPochhammer x a * realPochhammer (x + (a : ℝ)) b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.add_succ, realPochhammer_succ, ih, realPochhammer_succ]
    push_cast
    ring

/-- Shifting the starting argument of `realPochhammer` by $1$:
$(x)_{n + 1} = x \, (x + 1)_n$. -/
lemma realPochhammer_succ_left (x : ℝ) (n : ℕ) :
    realPochhammer x (n + 1) = x * realPochhammer (x + 1) n := by
  have h := realPochhammer_add x 1 n
  have h1 : realPochhammer x 1 = x := by
    rw [realPochhammer_succ, realPochhammer_zero, one_mul, Nat.cast_zero, add_zero]
  rw [Nat.add_comm 1 n, h1, Nat.cast_one] at h
  exact h

/-- `block1dCoeff` expressed in terms of `halfBinom`:
`block1dCoeff H n = halfBinom n * realPochhammer H n / realPochhammer (H + 1 / 2) n`. -/
lemma block1dCoeff_eq_halfBinom_mul_div (H : ℝ) (n : ℕ) :
    block1dCoeff H n = halfBinom n * realPochhammer H n / realPochhammer (H + 1 / 2) n := by
  dsimp [block1dCoeff, halfBinom]
  ring

/-- Unified Pochhammer cancellation identity for `block1dCoeff`: for $H > 1/2$ and any
$n, p \in \mathbb{N}$,
$$\operatorname{block1dCoeff}(H, n) \frac{(H - 1/2)_{n + 1 + p}}{(H)_{n + 1 + p}}
  = \left(H - \frac{1}{2}\right) \operatorname{halfBinom}(n)
    \frac{(H + n + 1/2)_p}{(H + n)_{p + 1}}.$$ -/
lemma block1dCoeff_mul_pochhammer_div_add_succ {H : ℝ} (hH : 1 / 2 < H) (n p : ℕ) :
    block1dCoeff H n *
        (realPochhammer (H - 1 / 2) (n + 1 + p) / realPochhammer H (n + 1 + p)) =
      (H - 1 / 2) * halfBinom n *
        (realPochhammer (H + (n : ℝ) + 1 / 2) p / realPochhammer (H + (n : ℝ)) (p + 1)) := by
  have hH_pos : 0 < H := by linarith
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
  have hA : A ≠ 0 := (realPochhammer_pos hH_pos n).ne'
  have hB : B ≠ 0 := (realPochhammer_pos hH_half_pos n).ne'
  have hD : D ≠ 0 := (realPochhammer_pos (by positivity) (p + 1)).ne'
  field_simp [hA, hB, hD]

/-- Pochhammer cancellation lemma for $m + 1 + k$. -/
lemma block1dCoeff_mul_pochhammer_div_succ {H : ℝ} (hH : 1 / 2 < H) (m k : ℕ) :
    block1dCoeff H k *
        (realPochhammer (H - 1 / 2) (m + 1 + k) / realPochhammer H (m + 1 + k)) =
      (H - 1 / 2) * halfBinom k *
        (realPochhammer (H + (k : ℝ) + 1 / 2) m /
          realPochhammer (H + (k : ℝ)) (m + 1)) := by
  have h_idx : m + 1 + k = k + 1 + m := by omega
  rw [h_idx, block1dCoeff_mul_pochhammer_div_add_succ hH k m]

/-- **Exact Vanishing of Higher Descendant Modes**:
For all $H > 1/2$ and all $m \ge 1$,
$$\sum_{n=0}^m b_{m - n} \, c_n(H) \frac{(H - 1/2)_{m + n}}{(H)_{m + n}}
  = \sum_{k=0}^{m - 1} b_{m - 1 - k} \, c_k(H) \frac{(H - 1/2)_{m + 1 + k}}{(H)_{m + 1 + k}}.$$ -/
theorem sum_transmuteCoeff_eq {H : ℝ} (hH : 1 / 2 < H) {m : ℕ} (hm : 1 ≤ m) :
    (∑ n ∈ Finset.range (m + 1),
      halfBinom (m - n) * block1dCoeff H n *
        (realPochhammer (H - 1 / 2) (m + n) / realPochhammer H (m + n))) =
    (∑ k ∈ Finset.range m,
      halfBinom (m - 1 - k) * block1dCoeff H k *
        (realPochhammer (H - 1 / 2) (m + 1 + k) / realPochhammer H (m + 1 + k))) := by
  have hH_pos : 0 < H := by linarith
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
      block1dCoeff_mul_pochhammer_div_succ hH p n,
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
      block1dCoeff_mul_pochhammer_div_succ hH (p + 1) k,
      ← sum_halfBinom_div_add_eq_pochhammer_div (p + 1)
        (fun n _ => by positivity : ∀ n ≤ p + 1, H + (k : ℝ) + (n : ℝ) ≠ 0),
      Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    have h_add : H + (k : ℝ) + (n : ℝ) = H + (n : ℝ) + (k : ℝ) := by ring
    rw [h_add]
    ring
  rw [h_lhs, h_rhs, Finset.sum_comm]

/-!
## 3. Transmutation Kernel, Beta Integral, and Action on `block1d`
-/

lemma norm_mul_exp_two_mul_lt_one {w : ℂ} (hw : w ∈ UcDisk) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) :
    ‖(s : ℂ) * Complex.exp (2 * w)‖ < 1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.1.le, Complex.norm_exp]
  have hre : (2 * w).re = 2 * w.re := by simp [Complex.mul_re]
  have hexp : Real.exp ((2 * w).re) < 1 := by
    rw [hre, Real.exp_lt_one_iff]
    linarith [mem_UcDisk_iff.mp hw]
  nlinarith [hs.1, hs.2, Real.exp_pos ((2 * w).re)]

/-- The core transmutation weight $\frac{\Gamma(H - 1/2)}{\Gamma(H)}$. -/
noncomputable def transmuteCoreWeight (H : ℝ) : ℝ :=
  Real.Gamma (H - 1 / 2) / Real.Gamma H

/-- The regularized transmutation weight
$w_0(H) = \left(H - \frac{1}{2}\right) \frac{\Gamma(H + 1/2)}{\Gamma(H)}$. -/
noncomputable def transmuteWeight (H : ℝ) : ℝ :=
  (H - 1 / 2) * Real.Gamma (H + 1 / 2) / Real.Gamma H

lemma transmuteWeight_pos {H : ℝ} (hH : 1 / 2 < H) :
    0 < transmuteWeight H := by
  dsimp [transmuteWeight]
  exact div_pos
    (mul_pos (by linarith) (Real.Gamma_pos_of_pos (by linarith)))
    (Real.Gamma_pos_of_pos (by linarith))

lemma transmuteWeight_eq_mul_transmuteCoreWeight {H : ℝ} (hH : 1 / 2 < H) :
    transmuteWeight H = (H - 1 / 2) ^ 2 * transmuteCoreWeight H := by
  dsimp [transmuteWeight, transmuteCoreWeight]
  have h_add : H + 1 / 2 = (H - 1 / 2) + 1 := by ring
  have h_ne : H - 1 / 2 ≠ 0 := by linarith
  rw [h_add, Real.Gamma_add_one h_ne]
  ring

/-- The 1D transmutation integral kernel on `UcDisk × Ioo 0 1`:
$$K(w, s) = s^{-3/2} (1 - s)^{-1/2} (1 - s^2 e^{2w}) (1 - s e^{2w})^{-1/2}.$$ -/
noncomputable def transmuteKernel (w : ℂ) (s : ℝ) : ℂ :=
  ((s ^ (-3 / 2 : ℝ) * (1 - s) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
    (1 - ((s ^ 2 : ℝ) : ℂ) * Complex.exp (2 * w)) *
    (1 - (s : ℂ) * Complex.exp (2 * w)) ^ (-1 / 2 : ℂ)

/-- The core 1D fractional transmutation operator acting via real log-translations on `UcDisk`:
$$(\operatorname{transmuteCore} f)(w)
  = \frac{1}{\sqrt{\pi}} \int_0^1 \operatorname{transmuteKernel}(w, s) \, f(w + \log s) \, ds.$$ -/
noncomputable def transmuteCore (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  ((Real.sqrt π : ℝ) : ℂ)⁻¹ *
    ∫ s in Ioo (0 : ℝ) 1, transmuteKernel w s * f (w + (Real.log s : ℂ))

/-- Real Gamma shift identity: for $x > 0$ and $N \in \mathbb{N}$,
$\Gamma(x + N) = \Gamma(x) \, (x)_N$. -/
lemma Gamma_add_nat_eq_mul_realPochhammer {x : ℝ} (hx : 0 < x) (N : ℕ) :
    Real.Gamma (x + (N : ℝ)) = Real.Gamma x * realPochhammer x N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h_add : x + ((N + 1 : ℕ) : ℝ) = (x + (N : ℝ)) + 1 := by push_cast; ring
    have h_ne : x + (N : ℝ) ≠ 0 := by positivity
    rw [h_add, Real.Gamma_add_one h_ne, ih, realPochhammer_succ]
    ring

/-- The real Beta integrand $s^{H + N - 3/2} (1 - s)^{-1/2}$ appearing in the transmutation of the
$N$-th mode. -/
noncomputable def betaKernel (H : ℝ) (N : ℕ) (s : ℝ) : ℝ :=
  s ^ (H + (N : ℝ) - 3 / 2) * (1 - s) ^ (-1 / 2 : ℝ)

lemma betaKernel_nonneg (H : ℝ) (N : ℕ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    0 ≤ betaKernel H N s := by
  dsimp [betaKernel]
  have hs0 : 0 < s := hs.1
  have hs1 : 0 < 1 - s := sub_pos.mpr hs.2
  positivity

lemma betaKernel_le_zero (H : ℝ) (N : ℕ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    betaKernel H N s ≤ betaKernel H 0 s := by
  dsimp [betaKernel]
  have hs1 : 0 < 1 - s := sub_pos.mpr hs.2
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  exact Real.rpow_le_rpow_of_exponent_ge hs.1 hs.2.le (by linarith)

lemma continuousOn_betaKernel (H : ℝ) (N : ℕ) :
    ContinuousOn (betaKernel H N) (Ioo (0 : ℝ) 1) := by
  intro s hs
  have h1 : ContinuousAt (fun x : ℝ => x ^ (H + (N : ℝ) - 3 / 2)) s :=
    continuousAt_id.rpow_const (Or.inl hs.1.ne')
  have h2 : ContinuousAt (fun x : ℝ => (1 - x) ^ (-1 / 2 : ℝ)) s :=
    (continuousAt_const.sub continuousAt_id).rpow_const (Or.inl (sub_pos.mpr hs.2).ne')
  exact (h1.mul h2).continuousWithinAt

lemma ofReal_betaKernel_eq (H : ℝ) (N : ℕ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    ((betaKernel H N s : ℝ) : ℂ) =
      (s : ℂ) ^ ((((H + (N : ℝ) - 1 / 2 : ℝ) : ℂ) - 1)) *
        (1 - (s : ℂ)) ^ (((1 / 2 : ℂ) - 1)) := by
  dsimp [betaKernel]
  have hs1 : 0 ≤ 1 - s := (sub_pos.mpr hs.2).le
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hs.1.le, Complex.ofReal_cpow hs1]
  congr 1
  · congr 1
    push_cast
    ring
  · congr 1
    · push_cast
      ring
    · push_cast
      ring

lemma integrableOn_betaKernel {H : ℝ} (hH : 1 / 2 < H) (N : ℕ) :
    IntegrableOn (betaKernel H N) (Ioo (0 : ℝ) 1) volume := by
  set u : ℂ := ((H + (N : ℝ) - 1 / 2 : ℝ) : ℂ)
  set v : ℂ := (1 / 2 : ℂ)
  have hu : 0 < u.re := by simp [u]; linarith
  have hv : 0 < v.re := by simp [v]
  have h_conv := (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
    (Complex.betaIntegral_convergent hu hv)
  have h_re : IntegrableOn
      (fun s : ℝ => ((s : ℂ) ^ (u - 1) * (1 - (s : ℂ)) ^ (v - 1)).re)
      (Ioo (0 : ℝ) 1) volume := h_conv.re
  refine h_re.congr_fun (fun s hs => ?_) measurableSet_Ioo
  have h_eq := congrArg Complex.re (ofReal_betaKernel_eq H N hs)
  rw [Complex.ofReal_re] at h_eq
  exact h_eq.symm

/-- Evaluation of the Beta integral on $s^{H + N - 3/2} (1 - s)^{-1/2}$ for $H > 1/2$ and
$N \in \mathbb{N}$:
$$\int_0^1 s^{H + N - 3/2} (1 - s)^{-1/2} \, ds
  = \sqrt{\pi} \, \operatorname{transmuteCoreWeight}(H)
    \frac{(H - 1/2)_N}{(H)_N}.$$ -/
theorem integral_betaKernel {H : ℝ} (hH : 1 / 2 < H) (N : ℕ) :
    (∫ s in Ioo (0 : ℝ) 1, betaKernel H N s) =
      Real.sqrt π * transmuteCoreWeight H *
        (realPochhammer (H - 1 / 2) N / realPochhammer H N) := by
  set u : ℂ := ((H + (N : ℝ) - 1 / 2 : ℝ) : ℂ)
  set v : ℂ := ((1 / 2 : ℝ) : ℂ)
  have hu : 0 < u.re := by simp [u]; linarith
  have hv : 0 < v.re := by simp [v]
  have h_c : (((∫ s in Ioo (0 : ℝ) 1, betaKernel H N s) : ℝ) : ℂ) =
      Complex.betaIntegral u v := by
    rw [← integral_complex_ofReal]
    have h_congr :
        (∫ s in Ioo (0 : ℝ) 1, (betaKernel H N s : ℂ)) =
          ∫ s in Ioo (0 : ℝ) 1, (s : ℂ) ^ (u - 1) * (1 - (s : ℂ)) ^ (v - 1) :=
      setIntegral_congr_fun measurableSet_Ioo fun s hs => by
        simpa [u, v] using ofReal_betaKernel_eq H N hs
    rw [h_congr, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_one]
    rfl
  rw [Complex.betaIntegral_eq_Gamma_mul_div u v hu hv] at h_c
  have hu_eq : u = (((H - 1 / 2) + (N : ℝ) : ℝ) : ℂ) := by dsimp [u]; push_cast; ring
  have huv_eq : u + v = ((H + (N : ℝ) : ℝ) : ℂ) := by dsimp [u, v]; push_cast; ring
  rw [huv_eq, hu_eq, Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal] at h_c
  have h_real :
      (∫ s in Ioo (0 : ℝ) 1, betaKernel H N s) =
        Real.Gamma ((H - 1 / 2) + (N : ℝ)) * Real.Gamma (1 / 2) /
          Real.Gamma (H + (N : ℝ)) := by
    exact_mod_cast h_c
  rw [h_real, Real.Gamma_one_half_eq,
    Gamma_add_nat_eq_mul_realPochhammer (by linarith : 0 < H - 1 / 2) N,
    Gamma_add_nat_eq_mul_realPochhammer (by linarith : 0 < H) N]
  dsimp [transmuteCoreWeight]
  ring

/-- The $m$-th mode coefficient sum before subtracting the $s^2 e^{2w}$ shift:
$$A_m(H) = \sum_{n=0}^m b_{m - n} \, c_n(H) \frac{(H - 1/2)_{m + n}}{(H)_{m + n}}.$$ -/
noncomputable def transmuteModeSum (H : ℝ) (m : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (m + 1),
    halfBinom (m - n) * block1dCoeff H n *
      (realPochhammer (H - 1 / 2) (m + n) / realPochhammer H (m + n))

@[simp]
lemma transmuteModeSum_zero (H : ℝ) : transmuteModeSum H 0 = 1 := by
  simp [transmuteModeSum]

lemma transmuteModeSum_nonneg {H : ℝ} (hH : 1 / 2 < H) (m : ℕ) :
    0 ≤ transmuteModeSum H m := by
  dsimp [transmuteModeSum]
  refine Finset.sum_nonneg fun n _ => ?_
  have h1 : 0 ≤ halfBinom (m - n) := halfBinom_nonneg (m - n)
  have h2 : 0 ≤ block1dCoeff H n := block1dCoeff_nonneg (by linarith) n
  have h3 : 0 ≤ realPochhammer (H - 1 / 2) (m + n) :=
    realPochhammer_nonneg (by linarith) (m + n)
  have h4 : 0 < realPochhammer H (m + n) :=
    realPochhammer_pos (by linarith) (m + n)
  positivity

lemma transmuteModeSum_le_succ {H : ℝ} (hH : 1 / 2 < H) (m : ℕ) :
    transmuteModeSum H m ≤ (m : ℝ) + 1 := by
  dsimp [transmuteModeSum]
  calc
    (∑ n ∈ Finset.range (m + 1),
      halfBinom (m - n) * block1dCoeff H n *
        (realPochhammer (H - 1 / 2) (m + n) / realPochhammer H (m + n)))
      ≤ ∑ _n ∈ Finset.range (m + 1), (1 : ℝ) := by
        refine Finset.sum_le_sum fun n _ => ?_
        have h1 : halfBinom (m - n) ≤ 1 := halfBinom_le_one (m - n)
        have h2 : block1dCoeff H n ≤ 1 := block1dCoeff_le_one (by linarith) n
        have h3 : realPochhammer (H - 1 / 2) (m + n) / realPochhammer H (m + n) ≤ 1 := by
          rw [div_le_one (realPochhammer_pos (by linarith) (m + n))]
          exact realPochhammer_mono (by linarith) (by linarith) (m + n)
        have h12 : halfBinom (m - n) * block1dCoeff H n ≤ 1 :=
          (mul_le_of_le_one_left (block1dCoeff_nonneg (by linarith) n) h1).trans h2
        have h3_nonneg :
            0 ≤ realPochhammer (H - 1 / 2) (m + n) / realPochhammer H (m + n) :=
          div_nonneg (realPochhammer_nonneg (by linarith) _)
            (realPochhammer_pos (by linarith) _).le
        exact (mul_le_of_le_one_left h3_nonneg h12).trans h3
    _ = (m : ℝ) + 1 := by simp

/-- The $m$-th mode integrand in the Cauchy product expansion of
`transmuteKernel w s * block1d H (w + Real.log s)`. -/
noncomputable def transmuteModeTerm (H : ℝ) (w : ℂ) (m : ℕ) (s : ℝ) : ℂ :=
  Complex.exp ((H : ℂ) * w) *
    ∑ n ∈ Finset.range (m + 1),
      ((halfBinom (m - n) * block1dCoeff H n : ℝ) : ℂ) *
        ((betaKernel H (m + n) s : ℂ) * (Complex.exp (2 * w)) ^ m -
          (betaKernel H (m + 2 + n) s : ℂ) * (Complex.exp (2 * w)) ^ (m + 1))

lemma continuousOn_transmuteModeTerm (H : ℝ) (w : ℂ) (m : ℕ) :
    ContinuousOn (transmuteModeTerm H w m) (Ioo (0 : ℝ) 1) := by
  unfold transmuteModeTerm
  refine continuousOn_const.mul (continuousOn_finsetSum _ fun n _ => ?_)
  refine continuousOn_const.mul (ContinuousOn.sub ?_ ?_)
  · exact (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_betaKernel H (m + n))).mul continuousOn_const
  · exact (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_betaKernel H (m + 2 + n))).mul continuousOn_const

lemma norm_transmuteModeTerm_le {H : ℝ} (hH : 1 / 2 < H) {w : ℂ} (hw : w ∈ UcDisk)
    (m : ℕ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    ‖transmuteModeTerm H w m s‖ ≤
      (2 * ((m : ℝ) + 1) * Real.exp (H * w.re) * (Real.exp (2 * w.re)) ^ m) *
        betaKernel H 0 s := by
  dsimp [transmuteModeTerm]
  rw [norm_mul, Complex.norm_exp]
  have h_re_H : ((H : ℂ) * w).re = H * w.re := by simp [Complex.mul_re]
  rw [h_re_H]
  have h_norm_q : ‖Complex.exp (2 * w)‖ = Real.exp (2 * w.re) := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re]
  have hq_le1 : Real.exp (2 * w.re) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith [mem_UcDisk_iff.mp hw])
  have h_bk0_nonneg : 0 ≤ betaKernel H 0 s := betaKernel_nonneg H 0 hs
  have h_sum_le :
      ‖∑ n ∈ Finset.range (m + 1),
        ((halfBinom (m - n) * block1dCoeff H n : ℝ) : ℂ) *
          ((betaKernel H (m + n) s : ℂ) * (Complex.exp (2 * w)) ^ m -
            (betaKernel H (m + 2 + n) s : ℂ) * (Complex.exp (2 * w)) ^ (m + 1))‖ ≤
        ((m : ℝ) + 1) * (2 * (Real.exp (2 * w.re)) ^ m * betaKernel H 0 s) := by
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
            (2 * (Real.exp (2 * w.re)) ^ m * betaKernel H 0 s) := by
          refine Finset.sum_le_sum fun n _ => ?_
          rw [norm_mul, Complex.norm_real,
            Real.norm_of_nonneg
              (mul_nonneg (halfBinom_nonneg _) (block1dCoeff_nonneg (by linarith) n))]
          have h_coeff : halfBinom (m - n) * block1dCoeff H n ≤ 1 :=
            (mul_le_of_le_one_left (block1dCoeff_nonneg (by linarith) n)
              (halfBinom_le_one (m - n))).trans (block1dCoeff_le_one (by linarith) n)
          have h_term1 :
              ‖(betaKernel H (m + n) s : ℂ) * (Complex.exp (2 * w)) ^ m‖ ≤
                betaKernel H 0 s * (Real.exp (2 * w.re)) ^ m := by
            rw [norm_mul, Complex.norm_real,
              Real.norm_of_nonneg (betaKernel_nonneg H (m + n) hs),
              norm_pow, h_norm_q]
            exact mul_le_mul_of_nonneg_right (betaKernel_le_zero H (m + n) hs) (by positivity)
          have h_term2 :
              ‖(betaKernel H (m + 2 + n) s : ℂ) * (Complex.exp (2 * w)) ^ (m + 1)‖ ≤
                betaKernel H 0 s * (Real.exp (2 * w.re)) ^ m := by
            rw [norm_mul, Complex.norm_real,
              Real.norm_of_nonneg (betaKernel_nonneg H (m + 2 + n) hs),
              norm_pow, h_norm_q, pow_succ]
            have h_pow_le : (Real.exp (2 * w.re)) ^ m * Real.exp (2 * w.re) ≤
                (Real.exp (2 * w.re)) ^ m * 1 :=
              mul_le_mul_of_nonneg_left hq_le1 (by positivity)
            rw [mul_one] at h_pow_le
            exact mul_le_mul (betaKernel_le_zero H (m + 2 + n) hs) h_pow_le
              (by positivity) h_bk0_nonneg
          have h_diff :
              ‖(betaKernel H (m + n) s : ℂ) * (Complex.exp (2 * w)) ^ m -
                (betaKernel H (m + 2 + n) s : ℂ) * (Complex.exp (2 * w)) ^ (m + 1)‖ ≤
                2 * (Real.exp (2 * w.re)) ^ m * betaKernel H 0 s := by
            calc
              ‖(betaKernel H (m + n) s : ℂ) * (Complex.exp (2 * w)) ^ m -
                (betaKernel H (m + 2 + n) s : ℂ) * (Complex.exp (2 * w)) ^ (m + 1)‖
                ≤ ‖(betaKernel H (m + n) s : ℂ) * (Complex.exp (2 * w)) ^ m‖ +
                    ‖(betaKernel H (m + 2 + n) s : ℂ) * (Complex.exp (2 * w)) ^ (m + 1)‖ :=
                  norm_sub_le _ _
              _ ≤ betaKernel H 0 s * (Real.exp (2 * w.re)) ^ m +
                    betaKernel H 0 s * (Real.exp (2 * w.re)) ^ m :=
                  add_le_add h_term1 h_term2
              _ = 2 * (Real.exp (2 * w.re)) ^ m * betaKernel H 0 s := by ring
          calc
            halfBinom (m - n) * block1dCoeff H n *
                ‖(betaKernel H (m + n) s : ℂ) * (Complex.exp (2 * w)) ^ m -
                  (betaKernel H (m + 2 + n) s : ℂ) * (Complex.exp (2 * w)) ^ (m + 1)‖
              ≤ 1 * (2 * (Real.exp (2 * w.re)) ^ m * betaKernel H 0 s) :=
                mul_le_mul h_coeff h_diff (norm_nonneg _) zero_le_one
            _ = 2 * (Real.exp (2 * w.re)) ^ m * betaKernel H 0 s := one_mul _
      _ = ((m : ℝ) + 1) * (2 * (Real.exp (2 * w.re)) ^ m * betaKernel H 0 s) := by
          simp
  calc
    Real.exp (H * w.re) *
        ‖∑ n ∈ Finset.range (m + 1),
          ((halfBinom (m - n) * block1dCoeff H n : ℝ) : ℂ) *
            ((betaKernel H (m + n) s : ℂ) * (Complex.exp (2 * w)) ^ m -
              (betaKernel H (m + 2 + n) s : ℂ) * (Complex.exp (2 * w)) ^ (m + 1))‖
      ≤ Real.exp (H * w.re) *
          (((m : ℝ) + 1) * (2 * (Real.exp (2 * w.re)) ^ m * betaKernel H 0 s)) :=
        mul_le_mul_of_nonneg_left h_sum_le (Real.exp_pos _).le
    _ = (2 * ((m : ℝ) + 1) * Real.exp (H * w.re) * (Real.exp (2 * w.re)) ^ m) *
          betaKernel H 0 s := by ring

/-- Pointwise series expansion of `transmuteKernel w s * block1d H (w + Real.log s)` into
`transmuteModeTerm H w m s` for $w \in \operatorname{UcDisk}$ and $s \in (0, 1)$. -/
lemma hasSum_transmuteModeTerm {H : ℝ} (hH : 1 / 2 < H) {w : ℂ} (hw : w ∈ UcDisk)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    HasSum (fun m : ℕ => transmuteModeTerm H w m s)
      (transmuteKernel w s * block1d H (w + (Real.log s : ℂ))) := by
  have hH_nonneg : 0 ≤ H := by linarith
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
      Real.norm_of_nonneg (mul_nonneg (block1dCoeff_nonneg hH_nonneg n) (by positivity)),
      norm_pow, hq_norm]
    have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hs_le : s ^ (H + 2 * (n : ℝ)) ≤ s ^ H :=
      Real.rpow_le_rpow_of_exponent_ge hs.1 hs.2.le (by linarith)
    have hc_le : block1dCoeff H n * s ^ (H + 2 * (n : ℝ)) ≤ s ^ H := by
      calc
        block1dCoeff H n * s ^ (H + 2 * (n : ℝ))
          ≤ 1 * s ^ H :=
            mul_le_mul (block1dCoeff_le_one hH_nonneg n) hs_le (by positivity) zero_le_one
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

/-- Exact Beta-integral evaluation of the $m$-th mode `transmuteModeTerm H w m`:
by `sum_transmuteCoeff_eq`, the integral of the $m$-th mode telescopes into
`transmuteModeSum H m * e^{2mw} - transmuteModeSum H (m + 1) * e^{2(m+1)w}`. -/
lemma inv_sqrt_pi_mul_integral_transmuteModeTerm {H : ℝ} (hH : 1 / 2 < H) (w : ℂ) (m : ℕ) :
    ((Real.sqrt π : ℝ) : ℂ)⁻¹ * (∫ s in Ioo (0 : ℝ) 1, transmuteModeTerm H w m s) =
      (transmuteCoreWeight H : ℂ) * Complex.exp ((H : ℂ) * w) *
        ((transmuteModeSum H m : ℂ) * (Complex.exp (2 * w)) ^ m -
          (transmuteModeSum H (m + 1) : ℂ) * (Complex.exp (2 * w)) ^ (m + 1)) := by
  dsimp [transmuteModeTerm]
  rw [integral_const_mul,
    integral_finsetSum (Finset.range (m + 1)) fun n _ => by
      refine Integrable.const_mul (Integrable.sub ?_ ?_) _
      · exact (integrableOn_betaKernel hH (m + n)).ofReal.mul_const _
      · exact (integrableOn_betaKernel hH (m + 2 + n)).ofReal.mul_const _]
  have h_each : ∀ n : ℕ,
      (∫ s in Ioo (0 : ℝ) 1,
        ((halfBinom (m - n) * block1dCoeff H n : ℝ) : ℂ) *
          ((betaKernel H (m + n) s : ℂ) * (Complex.exp (2 * w)) ^ m -
            (betaKernel H (m + 2 + n) s : ℂ) * (Complex.exp (2 * w)) ^ (m + 1))) =
      ((Real.sqrt π * transmuteCoreWeight H : ℝ) : ℂ) *
        ((((halfBinom (m - n) * block1dCoeff H n *
          (realPochhammer (H - 1 / 2) (m + n) / realPochhammer H (m + n)) : ℝ) : ℂ) *
            (Complex.exp (2 * w)) ^ m) -
          (((halfBinom (m - n) * block1dCoeff H n *
            (realPochhammer (H - 1 / 2) (m + 2 + n) / realPochhammer H (m + 2 + n)) : ℝ) : ℂ) *
            (Complex.exp (2 * w)) ^ (m + 1))) := by
    intro n
    have h1 : IntegrableOn
        (fun s : ℝ => (betaKernel H (m + n) s : ℂ) * (Complex.exp (2 * w)) ^ m)
        (Ioo (0 : ℝ) 1) volume :=
      (integrableOn_betaKernel hH (m + n)).ofReal.mul_const _
    have h2 : IntegrableOn
        (fun s : ℝ => (betaKernel H (m + 2 + n) s : ℂ) * (Complex.exp (2 * w)) ^ (m + 1))
        (Ioo (0 : ℝ) 1) volume :=
      (integrableOn_betaKernel hH (m + 2 + n)).ofReal.mul_const _
    rw [integral_const_mul, integral_sub h1 h2, integral_mul_const, integral_mul_const,
      integral_complex_ofReal, integral_complex_ofReal,
      integral_betaKernel hH (m + n),
      integral_betaKernel hH (m + 2 + n)]
    push_cast
    ring
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
    have h_eq := (sum_transmuteCoeff_eq hH (m := m + 1) (by omega)).symm
    simp only [Nat.add_sub_cancel] at h_eq
    have h_idx : ∀ x : ℕ, m + 1 + 1 + x = m + 2 + x := fun x => by omega
    simp_rw [h_idx] at h_eq
    have h_c := congrArg (fun r : ℝ => (r : ℂ)) h_eq
    simpa [transmuteModeSum] using h_c
  rw [h_sum1, h_sum2]
  have h_sqrt_ne : ((Real.sqrt π : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  push_cast
  field_simp [h_sqrt_ne]

lemma summable_mul_add_one_mul_exp_pow {w : ℂ} (hw : w ∈ UcDisk) :
    Summable (fun m : ℕ => ((m : ℝ) + 1) * (Real.exp (2 * w.re)) ^ m) := by
  have hw2 : 2 * w.re < 0 := by linarith [mem_UcDisk_iff.mp hw]
  have h_geom : Summable (fun m : ℕ =>
      (1 + (-(2 * w.re) / (2 * ((1 : ℝ) + 1)))⁻¹) ^ 1 *
        (Real.exp (2 * w.re / 2)) ^ m) := by
    apply Summable.mul_left
    apply summable_geometric_of_lt_one (by positivity)
    rw [Real.exp_lt_one_iff]
    linarith
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun m => ?_) h_geom
  have h_bd := one_add_natCast_pow_mul_exp_le 1 hw2 le_rfl m
  simpa [add_comm] using h_bd

/-- **Main 1D Fractional Transmutation Theorem (`transmuteCore_block1d`)**:
For all $H > 1/2$ and all $w \in \operatorname{UcDisk}$,
$$\operatorname{transmuteCore}(\operatorname{block1d} H)\, w
  = \operatorname{transmuteCoreWeight}(H) \, e^{H w}.$$ -/
theorem transmuteCore_block1d {H : ℝ} (hH : 1 / 2 < H) {w : ℂ} (hw : w ∈ UcDisk) :
    transmuteCore (block1d H) w =
      (transmuteCoreWeight H : ℂ) * Complex.exp ((H : ℂ) * w) := by
  set bound : ℕ → ℝ → ℝ := fun m s =>
    (2 * ((m : ℝ) + 1) * Real.exp (H * w.re) * (Real.exp (2 * w.re)) ^ m) *
      betaKernel H 0 s
  have h_sum_m :
      Summable (fun m : ℕ =>
        2 * ((m : ℝ) + 1) * Real.exp (H * w.re) * (Real.exp (2 * w.re)) ^ m) := by
    have h1 := (summable_mul_add_one_mul_exp_pow hw).mul_left (2 * Real.exp (H * w.re))
    refine h1.congr fun m => by ring
  have h_hasSum_int :
      HasSum
        (fun m : ℕ => ∫ s in Ioo (0 : ℝ) 1, transmuteModeTerm H w m s)
        (∫ s in Ioo (0 : ℝ) 1, transmuteKernel w s * block1d H (w + (Real.log s : ℂ))) := by
    refine MeasureTheory.hasSum_integral_of_dominated_convergence
      (μ := volume.restrict (Ioo (0 : ℝ) 1)) bound ?_ ?_ ?_ ?_ ?_
    · intro m
      exact (continuousOn_transmuteModeTerm H w m).aestronglyMeasurable measurableSet_Ioo
    · intro m
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact norm_transmuteModeTerm_le hH hw m hs
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s _
      exact h_sum_m.mul_right (betaKernel H 0 s)
    · have h_tsum :
          (fun s : ℝ => ∑' m : ℕ, bound m s) =
            fun s : ℝ =>
              (∑' m : ℕ,
                2 * ((m : ℝ) + 1) * Real.exp (H * w.re) * (Real.exp (2 * w.re)) ^ m) *
                betaKernel H 0 s := by
        ext s
        dsimp [bound]
        exact tsum_mul_right
      rw [h_tsum]
      exact (integrableOn_betaKernel hH 0).const_mul _
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact hasSum_transmuteModeTerm hH hw hs
  have h_scaled := h_hasSum_int.mul_left (((Real.sqrt π : ℝ) : ℂ)⁻¹)
  set c : ℕ → ℂ := fun m => (transmuteModeSum H m : ℂ) * (Complex.exp (2 * w)) ^ m
  have hc_summable : Summable c := by
    have h_dom := summable_mul_add_one_mul_exp_pow hw
    refine Summable.of_norm_bounded h_dom fun m => ?_
    dsimp [c]
    rw [norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (transmuteModeSum_nonneg hH m),
      norm_pow, Complex.norm_exp]
    have hre : (2 * w).re = 2 * w.re := by simp [Complex.mul_re]
    rw [hre]
    exact mul_le_mul_of_nonneg_right (transmuteModeSum_le_succ hH m) (by positivity)
  have hc_shift : HasSum (fun m : ℕ => c (m + 1)) ((∑' m : ℕ, c m) - c 0) := by
    simpa using (hasSum_nat_add_iff' 1).mpr hc_summable.hasSum
  have hc_tele : HasSum (fun m : ℕ => c m - c (m + 1)) 1 := by
    have h_sub := hc_summable.hasSum.sub hc_shift
    have hc0 : c 0 = 1 := by simp [c]
    rwa [sub_sub_cancel, hc0] at h_sub
  have h_tele_mul := hc_tele.mul_left ((transmuteCoreWeight H : ℂ) * Complex.exp ((H : ℂ) * w))
  rw [mul_one] at h_tele_mul
  have h_tele_congr :
      HasSum
        (fun m : ℕ =>
          ((Real.sqrt π : ℝ) : ℂ)⁻¹ * (∫ s in Ioo (0 : ℝ) 1, transmuteModeTerm H w m s))
        ((transmuteCoreWeight H : ℂ) * Complex.exp ((H : ℂ) * w)) := by
    refine h_tele_mul.congr_fun fun m => ?_
    rw [inv_sqrt_pi_mul_integral_transmuteModeTerm hH w m]
  exact h_scaled.unique h_tele_congr

/-- Integrability of `s ↦ transmuteKernel w s * block1d H (w + Real.log s)` on `Ioo 0 1`
for $H > 1/2$ and $w \in \operatorname{UcDisk}$. -/
lemma integrableOn_transmuteKernel_mul_block1d {H : ℝ} (hH : 1 / 2 < H)
    {w : ℂ} (hw : w ∈ UcDisk) :
    IntegrableOn
      (fun s : ℝ => transmuteKernel w s * block1d H (w + (Real.log s : ℂ)))
      (Ioo (0 : ℝ) 1) volume := by
  set bound : ℕ → ℝ → ℝ := fun m s =>
    (2 * ((m : ℝ) + 1) * Real.exp (H * w.re) * (Real.exp (2 * w.re)) ^ m) *
      betaKernel H 0 s
  have h_sum_m :
      Summable (fun m : ℕ =>
        2 * ((m : ℝ) + 1) * Real.exp (H * w.re) * (Real.exp (2 * w.re)) ^ m) := by
    have h1 := (summable_mul_add_one_mul_exp_pow hw).mul_left (2 * Real.exp (H * w.re))
    refine h1.congr fun m => by ring
  have h_dom_int :
      IntegrableOn (fun s : ℝ => ∑' m : ℕ, bound m s) (Ioo (0 : ℝ) 1) volume := by
    have h_tsum :
        (fun s : ℝ => ∑' m : ℕ, bound m s) =
          fun s : ℝ =>
            (∑' m : ℕ,
              2 * ((m : ℝ) + 1) * Real.exp (H * w.re) * (Real.exp (2 * w.re)) ^ m) *
              betaKernel H 0 s := by
      ext s
      dsimp [bound]
      exact tsum_mul_right
    rw [h_tsum]
    exact (integrableOn_betaKernel hH 0).const_mul _
  have h_meas : AEStronglyMeasurable
      (fun s : ℝ => transmuteKernel w s * block1d H (w + (Real.log s : ℂ)))
      (volume.restrict (Ioo (0 : ℝ) 1)) :=
    aestronglyMeasurable_of_tendsto_ae (u := atTop)
      (f := fun N s => ∑ m ∈ Finset.range N, transmuteModeTerm H w m s)
      (fun N => Finset.aestronglyMeasurable_fun_sum _ fun m _ =>
        (continuousOn_transmuteModeTerm H w m).aestronglyMeasurable measurableSet_Ioo)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
        exact (hasSum_transmuteModeTerm hH hw hs).tendsto_sum_nat)
  refine h_dom_int.mono' h_meas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have h_hs := hasSum_transmuteModeTerm hH hw hs
  rw [← h_hs.tsum_eq]
  have h_sum_b : Summable (fun m : ℕ => bound m s) := h_sum_m.mul_right (betaKernel H 0 s)
  have h_sum_norm : Summable (fun m : ℕ => ‖transmuteModeTerm H w m s‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun m => norm_transmuteModeTerm_le hH hw m hs) h_sum_b
  exact (norm_tsum_le_tsum_norm h_sum_norm).trans
    (h_sum_norm.tsum_le_tsum (fun m => norm_transmuteModeTerm_le hH hw m hs) h_sum_b)

/-- Scalar linearity of `transmuteCore`. -/
lemma transmuteCore_const_mul (c : ℂ) (f : ℂ → ℂ) (w : ℂ) :
    transmuteCore (fun z => c * f z) w = c * transmuteCore f w := by
  dsimp [transmuteCore]
  have h_pull :
      (fun s : ℝ => transmuteKernel w s * (c * f (w + (Real.log s : ℂ)))) =
        fun s : ℝ => c * (transmuteKernel w s * f (w + (Real.log s : ℂ))) := by
    ext s; ring
  rw [h_pull, integral_const_mul]
  ring

/-- Action of `transmuteCore` on a finite linear combination of 1D conformal blocks
(such as each lightcone twist level $g_m(w_r)$ of a `ConformalBlockLightcone`). -/
theorem transmuteCore_finset_sum_block1d {ι : Type*} (S : Finset ι)
    (c : ι → ℂ) (H : ι → ℝ) (hH : ∀ i ∈ S, 1 / 2 < H i)
    {w : ℂ} (hw : w ∈ UcDisk) :
    transmuteCore (fun z => ∑ i ∈ S, c i * block1d (H i) z) w =
      ∑ i ∈ S, c i * (transmuteCoreWeight (H i) : ℂ) * Complex.exp ((H i : ℂ) * w) := by
  dsimp [transmuteCore]
  have h_pull :
      (fun s : ℝ =>
        transmuteKernel w s * ∑ i ∈ S, c i * block1d (H i) (w + (Real.log s : ℂ))) =
      fun s : ℝ =>
        ∑ i ∈ S, c i * (transmuteKernel w s * block1d (H i) (w + (Real.log s : ℂ))) := by
    ext s
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [h_pull, integral_finsetSum S fun i hi =>
    (integrableOn_transmuteKernel_mul_block1d (hH i hi) hw).const_mul (c i),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [integral_const_mul]
  have h_i := transmuteCore_block1d (hH i hi) hw
  dsimp [transmuteCore] at h_i
  linear_combination c i * h_i

/-!
## 5. The $H$-Independent Operator `transmuteOp` ($\mathcal{L}_0$) and Non-Negative Weights
-/

/-- The shifted derivative operator $\bigl(\partial_w - \tfrac{1}{2}\bigr) f(w)$. -/
noncomputable def derivHalfSub (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  deriv f w - (1 / 2 : ℂ) * f w

/-- The $H$-independent 1D conformal block transmutation operator
$$\mathcal{L}_0(f)(w) :=
  \left(\partial_w - \frac{1}{2}\right)^2 \bigl(\operatorname{transmuteCore} f\bigr)(w).$$
Because `transmuteCore (block1d H) w = transmuteCoreWeight H * exp (H * w)` on the open half-plane
`UcDisk`, applying $\bigl(\partial_w - \tfrac{1}{2}\bigr)^2$ multiplies by $(H - 1/2)^2$ and turns
`transmuteCoreWeight H` into `transmuteWeight H` without any $H$-dependence in the operator. -/
noncomputable def transmuteOp (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  derivHalfSub (derivHalfSub (transmuteCore f)) w

/-- Local congruence of `derivHalfSub` on the open half-plane `UcDisk`. -/
lemma derivHalfSub_congr_ucDisk {f g : ℂ → ℂ} (hfg : ∀ z ∈ UcDisk, f z = g z) :
    ∀ w ∈ UcDisk, derivHalfSub f w = derivHalfSub g w := by
  intro w hw
  have h_ev : f =ᶠ[𝓝 w] g :=
    Filter.eventuallyEq_of_mem (isOpen_UcDisk.mem_nhds hw) hfg
  dsimp [derivHalfSub]
  rw [h_ev.deriv_eq, hfg w hw]

/-- Congruence of `transmuteOp` when `transmuteCore f` and `g` agree on `UcDisk`. -/
lemma transmuteOp_eq_of_transmuteCore_eq {f g : ℂ → ℂ}
    (hfg : ∀ z ∈ UcDisk, transmuteCore f z = g z) {w : ℂ} (hw : w ∈ UcDisk) :
    transmuteOp f w = derivHalfSub (derivHalfSub g) w := by
  dsimp [transmuteOp]
  have h1 : ∀ z ∈ UcDisk, derivHalfSub (transmuteCore f) z = derivHalfSub g z :=
    derivHalfSub_congr_ucDisk hfg
  exact derivHalfSub_congr_ucDisk h1 w hw

/-- Action of `derivHalfSub` on an exponential $z \mapsto c \, e^{H z}$. -/
lemma derivHalfSub_const_mul_exp (c : ℂ) (H : ℝ) (w : ℂ) :
    derivHalfSub (fun z : ℂ => c * Complex.exp ((H : ℂ) * z)) w =
      c * ((H - 1 / 2 : ℝ) : ℂ) * Complex.exp ((H : ℂ) * w) := by
  dsimp [derivHalfSub]
  have hd : HasDerivAt (fun z : ℂ => c * Complex.exp ((H : ℂ) * z))
      (c * ((H : ℂ) * Complex.exp ((H : ℂ) * w))) w := by
    have h1 : HasDerivAt (fun z : ℂ => (H : ℂ) * z) (H : ℂ) w := by
      simpa using (hasDerivAt_id w).const_mul (H : ℂ)
    have h2 : HasDerivAt (fun z : ℂ => Complex.exp ((H : ℂ) * z))
        (Complex.exp ((H : ℂ) * w) * (H : ℂ)) w := h1.cexp
    convert h2.const_mul c using 1
    ring
  rw [hd.deriv]
  push_cast
  ring

/-- Action of $\bigl(\partial_w - \tfrac{1}{2}\bigr)^2$ on $z \mapsto c \, e^{H z}$. -/
lemma derivHalfSub_derivHalfSub_const_mul_exp (c : ℂ) (H : ℝ) (w : ℂ) :
    derivHalfSub (derivHalfSub (fun z : ℂ => c * Complex.exp ((H : ℂ) * z))) w =
      c * ((H - 1 / 2 : ℝ) : ℂ) ^ 2 * Complex.exp ((H : ℂ) * w) := by
  have h1 : derivHalfSub (fun z : ℂ => c * Complex.exp ((H : ℂ) * z)) =
      fun z : ℂ => (c * ((H - 1 / 2 : ℝ) : ℂ)) * Complex.exp ((H : ℂ) * z) := by
    ext z
    exact derivHalfSub_const_mul_exp c H z
  rw [h1, derivHalfSub_const_mul_exp]
  ring

/-- **Main 1D transmutation theorem for the $H$-independent operator `transmuteOp`**
($\mathcal{L}_0$): for all $H > 1/2$ and $w \in \operatorname{UcDisk}$,
$$\operatorname{transmuteOp}(\operatorname{block1d} H)\, w =
  \operatorname{transmuteWeight}(H) \, e^{H w}.$$ -/
theorem transmuteOp_block1d {H : ℝ} (hH : 1 / 2 < H) {w : ℂ} (hw : w ∈ UcDisk) :
    transmuteOp (block1d H) w =
      (transmuteWeight H : ℂ) * Complex.exp ((H : ℂ) * w) := by
  rw [transmuteOp_eq_of_transmuteCore_eq
    (fun z hz => transmuteCore_block1d hH hz) hw]
  rw [derivHalfSub_derivHalfSub_const_mul_exp, transmuteWeight_eq_mul_transmuteCoreWeight hH]
  push_cast
  ring

/-- Scalar linearity of `derivHalfSub`. -/
lemma derivHalfSub_const_mul (c : ℂ) (f : ℂ → ℂ) (w : ℂ) :
    derivHalfSub (fun z => c * f z) w = c * derivHalfSub f w := by
  dsimp [derivHalfSub]
  rw [deriv_const_mul_field c]
  ring

/-- Action of `derivHalfSub` on a finite linear combination of exponentials. -/
lemma derivHalfSub_finset_sum_exp {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (H : ι → ℝ) (w : ℂ) :
    derivHalfSub (fun z : ℂ => ∑ i ∈ S, a i * Complex.exp ((H i : ℂ) * z)) w =
      ∑ i ∈ S, a i * ((H i - 1 / 2 : ℝ) : ℂ) * Complex.exp ((H i : ℂ) * w) := by
  dsimp [derivHalfSub]
  have hd : HasDerivAt (fun z : ℂ => ∑ i ∈ S, a i * Complex.exp ((H i : ℂ) * z))
      (∑ i ∈ S, a i * ((H i : ℂ) * Complex.exp ((H i : ℂ) * w))) w := by
    have h_fn : (fun z : ℂ => ∑ i ∈ S, a i * Complex.exp ((H i : ℂ) * z)) =
        ∑ i ∈ S, fun z : ℂ => a i * Complex.exp ((H i : ℂ) * z) := by
      ext z; simp
    rw [h_fn]
    refine HasDerivAt.sum fun i _ => ?_
    have h1 : HasDerivAt (fun z : ℂ => (H i : ℂ) * z) (H i : ℂ) w := by
      simpa using (hasDerivAt_id w).const_mul (H i : ℂ)
    convert h1.cexp.const_mul (a i) using 1
    ring
  rw [hd.deriv, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

/-- Scalar linearity of `transmuteOp`. -/
lemma transmuteOp_const_mul (c : ℂ) (f : ℂ → ℂ) (w : ℂ) :
    transmuteOp (fun z => c * f z) w = c * transmuteOp f w := by
  dsimp [transmuteOp]
  have h1 : transmuteCore (fun z => c * f z) = fun z => c * transmuteCore f z := by
    ext z; exact transmuteCore_const_mul c f z
  have h2 : derivHalfSub (fun z => c * transmuteCore f z) =
      fun z => c * derivHalfSub (transmuteCore f) z := by
    ext z; exact derivHalfSub_const_mul c (transmuteCore f) z
  rw [h1, h2, derivHalfSub_const_mul]

/-- Action of `transmuteOp` on a finite linear combination of 1D conformal blocks on `UcDisk`. -/
theorem transmuteOp_finset_sum_block1d {ι : Type*} (S : Finset ι)
    (c : ι → ℂ) (H : ι → ℝ) (hH : ∀ i ∈ S, 1 / 2 < H i)
    {w : ℂ} (hw : w ∈ UcDisk) :
    transmuteOp (fun z => ∑ i ∈ S, c i * block1d (H i) z) w =
      ∑ i ∈ S, c i * (transmuteWeight (H i) : ℂ) * Complex.exp ((H i : ℂ) * w) := by
  rw [transmuteOp_eq_of_transmuteCore_eq
    (fun z hz => transmuteCore_finset_sum_block1d S c H hH hz) hw]
  have h_step1 :
      derivHalfSub
        (fun z => ∑ i ∈ S, c i * (transmuteCoreWeight (H i) : ℂ) * Complex.exp ((H i : ℂ) * z)) =
      fun z =>
        ∑ i ∈ S, (c i * (transmuteCoreWeight (H i) : ℂ) * ((H i - 1 / 2 : ℝ) : ℂ)) *
          Complex.exp ((H i : ℂ) * z) := by
    ext z
    exact derivHalfSub_finset_sum_exp S (fun i => c i * (transmuteCoreWeight (H i) : ℂ)) H z
  rw [h_step1, derivHalfSub_finset_sum_exp]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [transmuteWeight_eq_mul_transmuteCoreWeight (hH i hi)]
  push_cast
  ring

/-- Non-negative truncation of `transmuteWeight H` at the unitarity threshold $H > 1/2$:
$$\operatorname{transmutePosWeight}(H) :=
  \begin{cases}
    \operatorname{transmuteWeight}(H) & \text{if } H > 1/2, \\
    0 & \text{otherwise.}
  \end{cases}$$
For every spin $J \ge 1$ and unitary left twist $h \ge 0$, $H = h + J \ge 1 > 1/2$, so
`transmutePosWeight (h + J) = transmuteWeight (h + J) > 0`. -/
noncomputable def transmutePosWeight (H : ℝ) : ℝ :=
  if 1 / 2 < H then transmuteWeight H else 0

lemma transmutePosWeight_of_gt {H : ℝ} (hH : 1 / 2 < H) :
    transmutePosWeight H = transmuteWeight H := by
  dsimp [transmutePosWeight]
  split_ifs
  · rfl
  · contradiction

lemma transmutePosWeight_nonneg (H : ℝ) :
    0 ≤ transmutePosWeight H := by
  dsimp [transmutePosWeight]
  split_ifs with hH
  · exact (transmuteWeight_pos hH).le
  · exact le_rfl

/-- `Real.Gamma` is continuous at every positive real number $x > 0$. -/
lemma continuousAt_real_Gamma_of_pos {x : ℝ} (hx : 0 < x) :
    ContinuousAt Real.Gamma x := by
  refine (Real.differentiableAt_Gamma fun m => ?_).continuousAt
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

/-- Continuity of `transmuteWeight` on $(1/2, \infty)$. -/
lemma continuousOn_transmuteWeight : ContinuousOn transmuteWeight (Ioi (1 / 2 : ℝ)) := by
  intro H hH
  rw [mem_Ioi] at hH
  unfold transmuteWeight
  refine ContinuousAt.continuousWithinAt ?_
  refine ContinuousAt.div ?_ (continuousAt_real_Gamma_of_pos (by linarith))
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  refine (continuousAt_id.sub continuousAt_const).mul ?_
  exact (continuousAt_real_Gamma_of_pos (by linarith)).comp
    (continuousAt_id.add continuousAt_const)

/-- Measurability of `transmutePosWeight`. -/
lemma measurable_transmutePosWeight : Measurable transmutePosWeight := by
  have h_eq : transmutePosWeight = (Ioi (1 / 2 : ℝ)).piecewise transmuteWeight (fun _ => 0) := by
    ext H
    rfl
  rw [h_eq]
  exact continuousOn_transmuteWeight.measurable_piecewise continuousOn_const measurableSet_Ioi

end CFT.LightconeBootstrap
