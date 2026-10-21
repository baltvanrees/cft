/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI-generated, edited by Balt van Rees
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import CFT.CutPlane
import CFT.Vitali
import CFT.Gegenbauers
import CFT.Blocks_1d
import CFT.Blocks

/-!
# Conformal blocks on the universal cover of the punctured polydisk `UcPdisk`

This file extends the Euclidean conformal blocks from `Blocks.lean`, which are defined there as
$G_Δ^{(l)}(ρ)$ with $ρ$ in the unit disk (so as functions of one complex variable),
to functions of two independent complex variables $(w_l, w_r)$ by analytic continuation.

These variables live in the
product of the two left half planes, so $\operatorname{Re}(w_l) < 0$ and
$\operatorname{Re}(w_r) < 0$. The corresponding domain is defined in `CutPlane.lean` as `UcPdisk`,
the universal cover of the punctured polydisk. The relation to the familiar $ρ$ and $\bar ρ$
variables is simply $(\rho, \bar \rho) = (e^{w_l}, e^{w_r})$.

In the first part of this file we implement this analytic continuation and prove its summability
(`ConformalBlock.summable_evalTermPdisk`) and joint holomorphy
(`ConformalBlock.differentiableOn_evalPdisk`):
- Using `geg_two_var_conj` from `Gegenbauers.lean`, the function at each descendant level $n$
  extends to an entire function `ConformalBlockLevel.evalTermPdisk` on
  $\mathbb{C} \times \mathbb{C}$. This function reproduces the corresponding function
  in the Euclidean block at level $n$ when $w_r = \bar{w}_l$.
- Positivity of the Gegenbauer expansion coefficients implies that for $\Delta \ge l$ on any
  half-polydisk $\operatorname{Re}(w_l) \le \sigma < 0, \operatorname{Re}(w_r) \le \sigma < 0$,
  the modulus of the level-$n$ contribution is bounded by its Euclidean radial value at
  $r = e^\sigma \in (0, 1)$ (`ConformalBlockLevel.norm_evalTermPdisk_le_evalTerm_of_re_le`).
- From this bound and radial summability (`ConformalBlock.summable_evalTerm_exp`), we deduce
  summability (`ConformalBlock.summable_evalTermPdisk`) and apply the locally dominated series
  holomorphy criterion `CFT.differentiableOn_tsum_of_differentiableOn_of_norm_le` from
  `Vitali.lean` to establish joint holomorphy (`ConformalBlock.differentiableOn_evalPdisk`).

In the second part we discuss the lightcone block decomposition of a $d$-dimensional conformal
block into one-dimensional ($SL(2, \mathbb{R})$) collinear conformal blocks from `Blocks_1d.lean`.
We in particular state that finitely many lightcone blocks appear at every twist level.
This will be important for the lightcone bootstrap, though the proof of this result in
`exists_conformalBlockLightcone` remains to be formalized.
-/

open Real Complex Topology Set Metric Polynomial
open scoped ComplexConjugate

/-!
## Polydisk Continuation of `ConformalBlock`

Using `geg_two_var_conj` from `Gegenbauers.lean`,
$$\|\rho\|^j C_j^\nu(\cos(\arg \rho)) = \sum_{a=0}^{j} c_{j, a}^\nu \rho^a \bar{\rho}^{j - a},$$
so every such term in the expansion of a `ConformalBlock` extends holomorphically to
$(w_l, w_r) \in \operatorname{UcPdisk}$ by replacing $(\rho, \bar{\rho})$ with
$(e^{w_l}, e^{w_r})$.
-/

namespace ConformalBlockLevel

variable {l n : ℕ} (lvl : ConformalBlockLevel l n)

/-- Polydisk evaluation of descendant level $n$ on $\operatorname{UcPdisk}$ using
`geg_two_var_sum`:
$$\sum_{j \in \text{descendantSpins}(l, n)} A_{n, j}
  e^{\frac{\Delta + n - j}{2} (w_l + w_r)}
  \operatorname{geg\_two\_var\_sum}\ \nu\ e^{w_l}\ e^{w_r}\ j.$$ -/
noncomputable def evalTermPdisk (ν Δ : ℝ) (wl wr : ℂ) : ℂ :=
  ∑ j ∈ descendantSpins l n,
    (lvl.A j : ℂ) *
      Complex.exp ((((Δ + (n : ℝ) - (j : ℝ)) / 2 : ℝ) : ℂ) * wl) *
      Complex.exp ((((Δ + (n : ℝ) - (j : ℝ)) / 2 : ℝ) : ℂ) * wr) *
      gegenbauer.geg_two_var_sum (ν : ℂ) (Complex.exp wl) (Complex.exp wr) j

/-- On the Euclidean section $w_r = \bar{w}$, `evalTermPdisk` agrees with the Euclidean
function `evalTerm` at $\rho = e^w$. This demonstrates equivalence at each
descendant level separately. -/
theorem evalTermPdisk_conj {ν : ℝ} (hν : 0 ≤ ν) (Δ : ℝ) (w : ℂ) :
    lvl.evalTermPdisk ν Δ w (conj w) = (lvl.evalTerm ν Δ (Complex.exp w) : ℂ) := by
  dsimp [evalTermPdisk, evalTerm, evalAngular, evalGegenbauer, cosArg]
  rw [Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.ofReal_mul]
  set ρ := Complex.exp w
  have hρ_norm : ‖ρ‖ = Real.exp w.re := Complex.norm_exp w
  have h_conj_ρ : Complex.exp (conj w) = conj ρ := Complex.exp_conj w
  have h_exp_prod :
      Complex.exp ((((Δ + (n : ℝ) - (j : ℝ)) / 2 : ℝ) : ℂ) * w) *
        Complex.exp ((((Δ + (n : ℝ) - (j : ℝ)) / 2 : ℝ) : ℂ) * conj w) =
      ((‖ρ‖ ^ (Δ + (n : ℝ) - (j : ℝ)) : ℝ) : ℂ) := by
    rw [← Complex.exp_add]
    have h_add :
        (((Δ + (n : ℝ) - (j : ℝ)) / 2 : ℝ) : ℂ) * w +
          (((Δ + (n : ℝ) - (j : ℝ)) / 2 : ℝ) : ℂ) * conj w =
        (((Δ + (n : ℝ) - (j : ℝ)) * w.re : ℝ) : ℂ) := by
      have hw : w + conj w = ((2 * w.re : ℝ) : ℂ) := Complex.add_conj w
      calc
        (((Δ + (n : ℝ) - (j : ℝ)) / 2 : ℝ) : ℂ) * w +
            (((Δ + (n : ℝ) - (j : ℝ)) / 2 : ℝ) : ℂ) * conj w
          = (((Δ + (n : ℝ) - (j : ℝ)) / 2 : ℝ) : ℂ) * (w + conj w) := by ring
        _ = (((Δ + (n : ℝ) - (j : ℝ)) / 2 : ℝ) : ℂ) * ((2 * w.re : ℝ) : ℂ) := by rw [hw]
        _ = (((Δ + (n : ℝ) - (j : ℝ)) * w.re : ℝ) : ℂ) := by push_cast; ring
    rw [h_add, ← Complex.ofReal_exp, hρ_norm, mul_comm _ w.re, Real.exp_mul]
  have h_geg := (gegenbauer.geg_two_var_conj (ν : ℂ) ρ j).symm
  have h_geg_real :
      (gegenbauer (ν : ℂ) j).eval (Real.cos ρ.arg : ℂ) =
        ((((gegenbauer (ν : ℂ) j).eval (Real.cos ρ.arg : ℂ)).re : ℝ) : ℂ) := by
    have h_im : ((gegenbauer (ν : ℂ) j).eval (Real.cos ρ.arg : ℂ)).im = 0 := by
      have h_sum_im : (gegenbauer.geg_two_var_sum (ν : ℂ) ρ (conj ρ) j).im = 0 := by
        dsimp [gegenbauer.geg_two_var_sum]
        have h_conj_sum :
            conj (∑ a ∈ Finset.range (j + 1),
              gegenbauer.geg_two_var_coeff (ν : ℂ) j a * ρ ^ a * (conj ρ) ^ (j - a)) =
            ∑ a ∈ Finset.range (j + 1),
              gegenbauer.geg_two_var_coeff (ν : ℂ) j a * ρ ^ a * (conj ρ) ^ (j - a) := by
          rw [map_sum]
          have h_flip := (Finset.sum_range_reflect
            (fun a => conj (gegenbauer.geg_two_var_coeff (ν : ℂ) j a * ρ ^ a * (conj ρ) ^ (j - a)))
            (j + 1)).symm
          rw [Nat.add_sub_cancel] at h_flip
          rw [h_flip]
          refine Finset.sum_congr rfl fun a ha => ?_
          have ha_le : a ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
          rcases gegenbauer.geg_two_var_coeff_is_nonneg_real ν hν j (j - a) with ⟨c, _, hc⟩
          have hc_symm :
              gegenbauer.geg_two_var_coeff (ν : ℂ) j (j - a) =
                gegenbauer.geg_two_var_coeff (ν : ℂ) j a := by
            dsimp [gegenbauer.geg_two_var_coeff]
            rw [Nat.sub_sub_self ha_le]
            ring
          simp only [map_mul, map_pow, conj_conj, Nat.sub_sub_self ha_le, hc, conj_ofReal]
          rw [← hc, hc_symm]
          ring
        exact Complex.conj_eq_iff_im.mp h_conj_sum
      have h_lhs_im :
          ((‖ρ‖ : ℂ) ^ j * (gegenbauer (ν : ℂ) j).eval (Real.cos ρ.arg : ℂ)).im = 0 := by
        rw [← h_geg]
        exact h_sum_im
      have h_pow_cast : (‖ρ‖ : ℂ) ^ j = ((‖ρ‖ ^ j : ℝ) : ℂ) := by norm_cast
      rw [h_pow_cast, Complex.im_ofReal_mul] at h_lhs_im
      exact (mul_eq_zero.mp h_lhs_im).resolve_left
        (pow_ne_zero j (by rw [hρ_norm]; exact Real.exp_ne_zero w.re))
    apply Complex.ext
    · rw [ofReal_re]
    · rw [h_im, ofReal_im]
  have h_rpow :
      ((‖ρ‖ ^ (Δ + (n : ℝ) - (j : ℝ)) : ℝ) : ℂ) * (‖ρ‖ : ℂ) ^ j =
        ((‖ρ‖ ^ (Δ + (n : ℝ)) : ℝ) : ℂ) := by
    have hρ_pos : 0 < ‖ρ‖ := by rw [hρ_norm]; exact Real.exp_pos w.re
    have h_real : ‖ρ‖ ^ (Δ + (n : ℝ) - (j : ℝ)) * ‖ρ‖ ^ j = ‖ρ‖ ^ (Δ + (n : ℝ)) := by
      rw [← Real.rpow_natCast ‖ρ‖ j, ← Real.rpow_add hρ_pos]
      ring_nf
    have h_cast : (‖ρ‖ : ℂ) ^ j = ((‖ρ‖ ^ j : ℝ) : ℂ) := by norm_cast
    rw [h_cast, ← Complex.ofReal_mul, h_real]
  calc
    (lvl.A j : ℂ) * Complex.exp ((((Δ + (n : ℝ) - (j : ℝ)) / 2 : ℝ) : ℂ) * w) *
        Complex.exp ((((Δ + (n : ℝ) - (j : ℝ)) / 2 : ℝ) : ℂ) * conj w) *
        gegenbauer.geg_two_var_sum (ν : ℂ) ρ (Complex.exp (conj w)) j
      = (lvl.A j : ℂ) *
          (Complex.exp ((((Δ + (n : ℝ) - (j : ℝ)) / 2 : ℝ) : ℂ) * w) *
            Complex.exp ((((Δ + (n : ℝ) - (j : ℝ)) / 2 : ℝ) : ℂ) * conj w)) *
          gegenbauer.geg_two_var_sum (ν : ℂ) ρ (conj ρ) j := by
        rw [h_conj_ρ]; ring
    _ = (lvl.A j : ℂ) * ((‖ρ‖ ^ (Δ + (n : ℝ) - (j : ℝ)) : ℝ) : ℂ) *
          ((‖ρ‖ : ℂ) ^ j *
            ((((gegenbauer (ν : ℂ) j).eval (Real.cos ρ.arg : ℂ)).re : ℝ) : ℂ)) := by
        rw [h_exp_prod, h_geg, ← h_geg_real]
    _ = (lvl.A j : ℂ) *
          (((‖ρ‖ ^ (Δ + (n : ℝ) - (j : ℝ)) : ℝ) : ℂ) * (‖ρ‖ : ℂ) ^ j) *
          ((((gegenbauer (ν : ℂ) j).eval (Real.cos ρ.arg : ℂ)).re : ℝ) : ℂ) := by ring
    _ = ((‖ρ‖ ^ (Δ + (n : ℝ)) : ℝ) : ℂ) *
          ((lvl.A j : ℂ) *
            ((((gegenbauer (ν : ℂ) j).eval (Real.cos ρ.arg : ℂ)).re : ℝ) : ℂ)) := by
        rw [h_rpow]; ring

end ConformalBlockLevel

namespace ConformalBlock

variable {ν Δ : ℝ} {l : ℕ} (B : ConformalBlock ν Δ l)

/-- Evaluation of a `ConformalBlock` continued to $(w_l, w_r) \in \operatorname{UcPdisk}$,
via a sum over descendant levels $n \in \mathbb{N}$. -/
noncomputable def evalPdisk (wl wr : ℂ) : ℂ :=
  ∑' n : ℕ, (B.level n).evalTermPdisk ν Δ wl wr

/-- On the Euclidean section $w_r = \bar{w}$, `B.evalPdisk` agrees with the Euclidean block
`B.eval` at $\rho = e^w$. A simple theorem to prove, given that we already have agreement at every
descendant level. -/
theorem evalPdisk_conj_eq_eval (hν : 0 ≤ ν) (w : ℂ) :
    B.evalPdisk w (conj w) = (B.eval (Complex.exp w) : ℂ) := by
  dsimp [evalPdisk, eval]
  rw [Complex.ofReal_tsum]
  exact tsum_congr fun n => (B.level n).evalTermPdisk_conj hν Δ w

-- /-- For $z \in \text{CutPlane}$, evaluating the block `B.evalPdisk` at
-- $(\operatorname{logRho}(z), \overline{\operatorname{logRho}(z)})$ agrees with the Euclidean
-- block `B.eval (rho z)`. This theorem is unused at the moment.
-- -/
-- theorem evalPdisk_logRho_conj (hν : 0 ≤ ν) {z : ℂ} (hz : z ∈ CutPlane) :
--     B.evalPdisk (logRho z) (conj (logRho z)) = (B.eval (rho z) : ℂ) := by
--   rw [B.evalPdisk_conj_eq_eval hν (logRho z), exp_logRho hz]

/-- Level-wise triangle inequality bound for `lvl.evalTermPdisk`: when
$\operatorname{Re}(w_l) \le \sigma$ and $\operatorname{Re}(w_r) \le \sigma$, we have a bound
of the level $n$ descendant contribution in terms of the Euclidean level $n$ descendant
contribution evaluated at $ρ = e^\sigma$. -/
theorem _root_.ConformalBlockLevel.norm_evalTermPdisk_le_evalTerm_of_re_le {l n : ℕ}
    (lvl : ConformalBlockLevel l n) (hν : 0 ≤ ν) (hΔ : (l : ℝ) ≤ Δ)
    {wl wr : ℂ} {σ : ℝ} (hwl : wl.re ≤ σ) (hwr : wr.re ≤ σ) :
    ‖lvl.evalTermPdisk ν Δ wl wr‖ ≤
      lvl.evalTerm ν Δ (Real.exp σ : ℂ) := by
  dsimp [ConformalBlockLevel.evalTermPdisk, ConformalBlockLevel.evalTerm,
    ConformalBlockLevel.evalAngular, evalGegenbauer, cosArg]
  set r : ℝ := Real.exp σ
  have hr_pos : 0 < r := Real.exp_pos _
  have hr_norm : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_of_nonneg hr_pos.le]
  have hr_arg : (r : ℂ).arg = 0 := Complex.arg_ofReal_of_nonneg hr_pos.le
  rw [hr_norm, hr_arg, Real.cos_zero, Complex.ofReal_one, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  have hj_le : j ≤ l + n := (mem_descendantSpins.mp hj).2.1
  have h_exp_nonneg : 0 ≤ (Δ + (n : ℝ) - (j : ℝ)) / 2 := by
    have hj_real : (j : ℝ) ≤ (l : ℝ) + (n : ℝ) := by exact_mod_cast hj_le
    linarith
  have h_A_nonneg : 0 ≤ lvl.A j := lvl.A_nonneg j hj
  simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg h_A_nonneg, Complex.norm_exp,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have h_exp_wl :
      Real.exp ((Δ + (n : ℝ) - (j : ℝ)) / 2 * wl.re) ≤
        Real.exp ((Δ + (n : ℝ) - (j : ℝ)) / 2 * σ) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hwl h_exp_nonneg)
  have h_exp_wr :
      Real.exp ((Δ + (n : ℝ) - (j : ℝ)) / 2 * wr.re) ≤
        Real.exp ((Δ + (n : ℝ) - (j : ℝ)) / 2 * σ) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hwr h_exp_nonneg)
  have h_geg1 :
      ‖gegenbauer.geg_two_var_sum (ν : ℂ) (Complex.exp wl) (Complex.exp wr) j‖ ≤
        r ^ j * ((gegenbauer (ν : ℂ) j).eval 1).re := by
    have h1 := gegenbauer.norm_geg_two_var_sum_le ν hν (Complex.exp wl) (Complex.exp wr) j
    have h2 := gegenbauer.geg_two_var_sum_le_max_R ν hν
      ‖Complex.exp wl‖ ‖Complex.exp wr‖ (norm_nonneg _) (norm_nonneg _) j
    have h_max_le : max ‖Complex.exp wl‖ ‖Complex.exp wr‖ ≤ r := by
      rw [Complex.norm_exp, Complex.norm_exp]
      exact max_le (Real.exp_le_exp.mpr hwl) (Real.exp_le_exp.mpr hwr)
    have h_geg_one :
        (gegenbauer.geg_two_var_sum (ν : ℂ) 1 1 j).re = ((gegenbauer (ν : ℂ) j).eval 1).re := by
      have h_conj := (gegenbauer.geg_two_var_conj (ν : ℂ) 1 j).symm
      simp only [norm_one, ofReal_one, one_pow, one_mul, arg_one, Real.cos_zero, map_one] at h_conj
      exact congrArg Complex.re h_conj
    have h_geg_nonneg : 0 ≤ ((gegenbauer (ν : ℂ) j).eval 1).re := by
      rw [← h_geg_one]
      have h_11 := gegenbauer.norm_geg_two_var_sum_le ν hν 1 1 j
      simpa using (norm_nonneg _).trans h_11
    rw [h_geg_one] at h2
    exact (h1.trans h2).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (le_max_of_le_left (norm_nonneg _)) h_max_le j) h_geg_nonneg)
  have h_exp_r :
      Real.exp ((Δ + (n : ℝ) - (j : ℝ)) / 2 * σ) *
        Real.exp ((Δ + (n : ℝ) - (j : ℝ)) / 2 * σ) * r ^ j =
      r ^ (Δ + (n : ℝ)) := by
    rw [← Real.exp_add]
    have h_sum :
        (Δ + (n : ℝ) - (j : ℝ)) / 2 * σ + (Δ + (n : ℝ) - (j : ℝ)) / 2 * σ =
        σ * (Δ + (n : ℝ) - (j : ℝ)) := by ring
    rw [h_sum, Real.exp_mul, ← Real.rpow_natCast r j, ← Real.rpow_add hr_pos]
    congr 1
    ring
  calc
    lvl.A j * Real.exp ((Δ + (n : ℝ) - (j : ℝ)) / 2 * wl.re) *
        Real.exp ((Δ + (n : ℝ) - (j : ℝ)) / 2 * wr.re) *
        ‖gegenbauer.geg_two_var_sum (ν : ℂ) (Complex.exp wl) (Complex.exp wr) j‖
      ≤ lvl.A j * Real.exp ((Δ + (n : ℝ) - (j : ℝ)) / 2 * σ) *
          Real.exp ((Δ + (n : ℝ) - (j : ℝ)) / 2 * σ) *
          (r ^ j * ((gegenbauer (ν : ℂ) j).eval 1).re) := by
        have h_prod1 :
            lvl.A j * Real.exp ((Δ + (n : ℝ) - (j : ℝ)) / 2 * wl.re) ≤
              lvl.A j * Real.exp ((Δ + (n : ℝ) - (j : ℝ)) / 2 * σ) :=
          mul_le_mul_of_nonneg_left h_exp_wl h_A_nonneg
        have h_prod2 :
            lvl.A j * Real.exp ((Δ + (n : ℝ) - (j : ℝ)) / 2 * wl.re) *
                Real.exp ((Δ + (n : ℝ) - (j : ℝ)) / 2 * wr.re) ≤
              lvl.A j * Real.exp ((Δ + (n : ℝ) - (j : ℝ)) / 2 * σ) *
                Real.exp ((Δ + (n : ℝ) - (j : ℝ)) / 2 * σ) :=
          mul_le_mul h_prod1 h_exp_wr (Real.exp_pos _).le (by positivity)
        exact mul_le_mul h_prod2 h_geg1 (norm_nonneg _) (by positivity)
    _ = lvl.A j *
          (Real.exp ((Δ + (n : ℝ) - (j : ℝ)) / 2 * σ) *
            Real.exp ((Δ + (n : ℝ) - (j : ℝ)) / 2 * σ) * r ^ j) *
          ((gegenbauer (ν : ℂ) j).eval 1).re := by ring
    _ = r ^ (Δ + (n : ℝ)) * (lvl.A j * ((gegenbauer (ν : ℂ) j).eval 1).re) := by
        rw [h_exp_r]
        ring

/-- Same bound, but with $\sigma = \max(\operatorname{Re}(w_l), \operatorname{Re}(w_r))$ and
$r = e^{\max(\operatorname{Re}(w_l), \operatorname{Re}(w_r))}$. -/
theorem _root_.ConformalBlockLevel.norm_evalTermPdisk_le_evalTerm {l n : ℕ}
    (lvl : ConformalBlockLevel l n) (hν : 0 ≤ ν) (hΔ : (l : ℝ) ≤ Δ)
    {wl wr : ℂ} (_hwl : wl ∈ UcDisk) (_hwr : wr ∈ UcDisk) :
    ‖lvl.evalTermPdisk ν Δ wl wr‖ ≤
      lvl.evalTerm ν Δ (Real.exp (max wl.re wr.re) : ℂ) :=
  lvl.norm_evalTermPdisk_le_evalTerm_of_re_le hν hΔ (le_max_left _ _) (le_max_right _ _)

/-- Summability of the Euclidean descendant series on the positive real axis at $r = e^\sigma$ for
$\sigma < 0$. -/
lemma summable_evalTerm_exp {σ : ℝ} (hσ : σ < 0) :
    Summable (fun n : ℕ => (B.level n).evalTerm ν Δ (Real.exp σ : ℂ)) := by
  set r : ℝ := Real.exp σ
  have hr_pos : 0 < r := Real.exp_pos _
  have h_radial_eq : ∀ n : ℕ,
      (B.level n).evalTerm ν Δ (r : ℂ) = r ^ (Δ + (n : ℝ)) * (B.level n).evalAngular ν 1 := by
    intro n
    dsimp [ConformalBlockLevel.evalTerm, cosArg]
    rw [Complex.norm_real, Real.norm_of_nonneg hr_pos.le,
      Complex.arg_ofReal_of_nonneg hr_pos.le, Real.cos_zero]
  simp_rw [h_radial_eq]
  exact B.summable_radial r ⟨hr_pos, Real.exp_lt_one_iff.mpr hσ⟩

/-- Same bound, now for the entire block on the polydisk, in terms of the Euclidean conformal
block. -/
theorem norm_evalPdisk_le_eval_of_re_le (hν : 0 ≤ ν) (hΔ : (l : ℝ) ≤ Δ) {wl wr : ℂ}
    {σ : ℝ} (hσ : σ < 0) (hwl : wl.re ≤ σ) (hwr : wr.re ≤ σ) :
    ‖B.evalPdisk wl wr‖ ≤ B.eval (Real.exp σ : ℂ) := by
  dsimp [evalPdisk, eval]
  have h_sum_rhs := B.summable_evalTerm_exp hσ
  have h_term_bound : ∀ n : ℕ,
      ‖(B.level n).evalTermPdisk ν Δ wl wr‖ ≤ (B.level n).evalTerm ν Δ (Real.exp σ : ℂ) :=
    fun n => (B.level n).norm_evalTermPdisk_le_evalTerm_of_re_le hν hΔ hwl hwr
  have h_sum_norm : Summable (fun n : ℕ => ‖(B.level n).evalTermPdisk ν Δ wl wr‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) h_term_bound h_sum_rhs
  exact (norm_tsum_le_tsum_norm h_sum_norm).trans
    (h_sum_norm.tsum_le_tsum h_term_bound h_sum_rhs)

/-- Same bound for the entire block, with $\sigma = \max(\operatorname{Re}(w_l),
\operatorname{Re}(w_r))$ and $r = e^{\max(\operatorname{Re}(w_l), \operatorname{Re}(w_r))}$. -/
theorem norm_evalPdisk_le_eval (hν : 0 ≤ ν) (hΔ : (l : ℝ) ≤ Δ) {wl wr : ℂ}
    (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) :
    ‖B.evalPdisk wl wr‖ ≤ B.eval (Real.exp (max wl.re wr.re) : ℂ) :=
  B.norm_evalPdisk_le_eval_of_re_le hν hΔ (max_lt hwl hwr) (le_max_left _ _) (le_max_right _ _)

/-- An important lemma: summability of the descendant level series for
`B.evalPdisk` at any point of $\operatorname{UcPdisk}$. -/
lemma summable_evalTermPdisk (hν : 0 ≤ ν) (hΔ : (l : ℝ) ≤ Δ) {wl wr : ℂ}
    (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) :
    Summable (fun n : ℕ => (B.level n).evalTermPdisk ν Δ wl wr) :=
  Summable.of_norm_bounded (B.summable_evalTerm_exp (max_lt hwl hwr)) fun n =>
    (B.level n).norm_evalTermPdisk_le_evalTerm_of_re_le
      hν hΔ (le_max_left _ _) (le_max_right _ _)


/-! ## Joint holomorphy-/

/-- We have joint holomorphy of every level function `lvl.evalTermPdisk`
on $\mathbb{C} \times \mathbb{C}$. Easy theorem by `fun_prop`. -/
theorem _root_.ConformalBlockLevel.differentiable_evalTermPdisk {l n : ℕ}
    (lvl : ConformalBlockLevel l n) (ν Δ : ℝ) :
    Differentiable ℂ (fun w : ℂ × ℂ => lvl.evalTermPdisk ν Δ w.1 w.2) := by
  dsimp [ConformalBlockLevel.evalTermPdisk, gegenbauer.geg_two_var_sum]
  fun_prop

/-- Every point $w_0 \in \operatorname{UcPdisk}$ has a closed ball $\overline{B}(w_0, \delta)
\subseteq \operatorname{UcPdisk}$ on which both coordinates have real part bounded above by some
$\sigma < 0$. -/
lemma _root_.exists_closedBall_subset_UcPdisk {w₀ : ℂ × ℂ} (hw₀ : w₀ ∈ UcPdisk) :
    ∃ δ > 0, ∃ σ < (0 : ℝ), closedBall w₀ δ ⊆ UcPdisk ∧
      ∀ w ∈ closedBall w₀ δ, w.1.re ≤ σ ∧ w.2.re ≤ σ := by
  set σ₀ : ℝ := max w₀.1.re w₀.2.re
  have hσ₀ : σ₀ < 0 := max_lt hw₀.1 hw₀.2
  set σ : ℝ := σ₀ / 2
  have hσ : σ < 0 := by dsimp [σ]; linarith
  set δ : ℝ := -σ
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have h_re : ∀ w ∈ closedBall w₀ δ, w.1.re ≤ σ ∧ w.2.re ≤ σ := by
    intro w hw
    rw [mem_closedBall, Prod.dist_eq, max_le_iff] at hw
    have h1 : w.1.re - w₀.1.re ≤ δ := by
      calc
        w.1.re - w₀.1.re = (w.1 - w₀.1).re := by simp
        _ ≤ ‖w.1 - w₀.1‖ := Complex.re_le_norm _
        _ = dist w.1 w₀.1 := (dist_eq_norm _ _).symm
        _ ≤ δ := hw.1
    have h2 : w.2.re - w₀.2.re ≤ δ := by
      calc
        w.2.re - w₀.2.re = (w.2 - w₀.2).re := by simp
        _ ≤ ‖w.2 - w₀.2‖ := Complex.re_le_norm _
        _ = dist w.2 w₀.2 := (dist_eq_norm _ _).symm
        _ ≤ δ := hw.2
    have hw₀1 : w₀.1.re ≤ σ₀ := le_max_left _ _
    have hw₀2 : w₀.2.re ≤ σ₀ := le_max_right _ _
    refine ⟨by dsimp [δ, σ] at h1 ⊢; linarith, by dsimp [δ, σ] at h2 ⊢; linarith⟩
  refine ⟨δ, hδ, σ, hσ, ?_, h_re⟩
  intro w hw
  obtain ⟨h1, h2⟩ := h_re w hw
  exact ⟨lt_of_le_of_lt h1 hσ, lt_of_le_of_lt h2 hσ⟩

/-- An important theorem: joint holomorphy of the block `B.evalPdisk` on
$\operatorname{UcPdisk}$. -/
theorem differentiableOn_evalPdisk (hν : 0 ≤ ν) (hΔ : (l : ℝ) ≤ Δ) :
    DifferentiableOn ℂ (fun w : ℂ × ℂ => B.evalPdisk w.1 w.2) UcPdisk := by
  dsimp [evalPdisk]
  refine CFT.differentiableOn_tsum_of_differentiableOn_of_norm_le isOpen_UcPdisk
    (fun n => ((B.level n).differentiable_evalTermPdisk ν Δ).differentiableOn) ?_
  intro w₀ hw₀
  obtain ⟨δ, hδ, σ, hσ, h_sub, h_re⟩ := exists_closedBall_subset_UcPdisk hw₀
  refine ⟨δ, hδ, h_sub, fun n => (B.level n).evalTerm ν Δ (Real.exp σ : ℂ),
    B.summable_evalTerm_exp hσ, fun n w hw => ?_⟩
  obtain ⟨hw1, hw2⟩ := h_re w hw
  exact (B.level n).norm_evalTermPdisk_le_evalTerm_of_re_le hν hΔ hw1 hw2

end ConformalBlock

/-!
## Lightcone conformal block decomposition into one-dimensional conformal blocks

Consider the lightcone expansion on $\operatorname{UcPdisk}$:
$$G_{\Delta, l}(e^{w_l}, e^{w_r}) =
  \sum_{m=0}^{\infty} e^{((\Delta - l)/2 + m) w_l} g_m(w_r),$$
We claim, though it is not yet proven, that the leading twist function $g_0(w_r)$ is proportional
to a single one-dimensional conformal block $k_{(\Delta + l)/2}(e^{w_r})$ from `Blocks_1d.lean`,
while each subleading twist function
$g_m(w_r)$ ($m > 0$) is a *finite* linear combination of 1D conformal blocks
$k_{(\Delta - l)/2 + k_r}(e^{w_r})$ with non-negative coefficients.
-/

/-- Left/right scaling exponent $h(k) = \frac{\Delta - l}{2} + k$. -/
noncomputable def blockExp (Δ : ℝ) (l k : ℕ) : ℝ :=
  (Δ - (l : ℝ)) / 2 + (k : ℝ)

/-- Data for a single left-moving twist level $m$ in the lightcone expansion of a conformal block.
Captures the right-moving function $g_m(w_r)$ as a finite linear combination of 1D conformal
blocks $k_{\bar{h}}(e^{w_r})$ with non-negative coefficients. -/
structure ConformalBlockLightconeLevel where
  /-- Finite set of right-moving shift indices $k_r \in \mathbb{N}$ appearing in $g_m(w_r)$,
  corresponding to 1D conformal blocks of weight $\bar{h} = \text{blockExp}\ \Delta\ l\ k_r$. -/
  support : Finset ℕ
  /-- Coefficient $C_{m, k_r}$ of the 1D conformal block $k_{\text{blockExp}\ \Delta\ l\ k_r}$. -/
  C : ℕ → ℝ
  /-- Non-negativity of the 1D block coefficients: $C_{m, k_r} \ge 0$. -/
  C_nonneg : ∀ kr ∈ support, 0 ≤ C kr
  /-- Coefficients vanish outside `support`. -/
  C_support : ∀ kr ∉ support, C kr = 0

namespace ConformalBlockLightconeLevel

variable (lvl : ConformalBlockLightconeLevel)

/-- Evaluation of the right-moving function $g_m(w_r)$ as a finite linear combination of
1D conformal blocks:
$$g_m(w_r) = \sum_{k_r \in \text{support}} C_{m, k_r} \,
  k_{(\Delta - l)/2 + k_r}(e^{w_r}).$$ -/
noncomputable def eval (Δ : ℝ) (l : ℕ) (wr : ℂ) : ℂ :=
  ∑ kr ∈ lvl.support, (lvl.C kr : ℂ) * block1d (blockExp Δ l kr) wr

end ConformalBlockLightconeLevel

/-- Lightcone decomposition of a conformal block $G_{\Delta, l}(e^{w_l}, e^{w_r})$ into
one-dimensional conformal blocks:
$$G_{\Delta, l}(e^{w_l}, e^{w_r}) =
  \sum_{m=0}^{\infty} e^{((\Delta - l)/2 + m) w_l} g_m(w_r),$$
where $g_0(w_r) = C_{0, l} \, k_{(\Delta + l)/2}(e^{w_r})$ is a single 1D conformal block and
every $g_m(w_r)$ for $m > 0$ is a finite linear combination of 1D conformal blocks with
non-negative coefficients. -/
structure ConformalBlockLightcone (Δ : ℝ) (l : ℕ) where
  /-- Lightcone level data $g_m$ for each left-moving twist level $m \in \mathbb{N}$. -/
  level : ℕ → ConformalBlockLightconeLevel
  /-- Leading twist ($m = 0$) consists of a single 1D conformal block at $k_r = l$
  (weight $\bar{h} = (\Delta + l) / 2$). -/
  support_zero : (level 0).support = {l}
  /-- Positivity of the leading 1D conformal block coefficient $C_{0, l} > 0$. -/
  C_zero_pos : 0 < (level 0).C l
  /-- Summability of the lightcone expansion on the real negative half-lines
  $x_l < 0, x_r < 0$. -/
  summable_real : ∀ xl < (0 : ℝ), ∀ xr < (0 : ℝ),
    Summable (fun m : ℕ =>
      Real.exp (blockExp Δ l m * xl) * ‖(level m).eval Δ l (xr : ℂ)‖)

namespace ConformalBlockLightcone

variable {Δ : ℝ} {l : ℕ} (L : ConformalBlockLightcone Δ l)

/-- Evaluation of the right-moving function $g_m(w_r)$ at twist level $m$. -/
noncomputable def evalLevel (m : ℕ) (wr : ℂ) : ℂ :=
  (L.level m).eval Δ l wr

/-- Evaluation of the full conformal block via its lightcone expansion on $\operatorname{UcPdisk}$:
$$\sum_{m=0}^{\infty} e^{((\Delta - l)/2 + m) w_l} g_m(w_r).$$ -/
noncomputable def eval (wl wr : ℂ) : ℂ :=
  ∑' m : ℕ, Complex.exp ((blockExp Δ l m : ℂ) * wl) * L.evalLevel m wr

/-- At leading twist $m = 0$, $g_0(w_r)$ is a single 1D conformal block of weight
$\bar{h} = (\Delta + l) / 2$. -/
lemma evalLevel_zero (wr : ℂ) :
    L.evalLevel 0 wr = ((L.level 0).C l : ℂ) * block1d ((Δ + (l : ℝ)) / 2) wr := by
  dsimp [evalLevel, ConformalBlockLightconeLevel.eval, blockExp]
  rw [L.support_zero, Finset.sum_singleton]
  congr 2
  ring

end ConformalBlockLightcone

namespace ConformalBlock

variable {ν Δ : ℝ} {l : ℕ} (B : ConformalBlock ν Δ l)

/-- Every conformal block continued to $\operatorname{UcPdisk}$ admits a lightcone decomposition
into finite non-negative sums of one-dimensional conformal blocks at each left-moving twist
level $m$. Proof at the moment is `sorry`. -/
theorem exists_conformalBlockLightcone (hν : 0 < ν) (hΔ : (l : ℝ) ≤ Δ) :
    ∃ L : ConformalBlockLightcone Δ l,
      ∀ wl ∈ UcDisk, ∀ wr ∈ UcDisk,
        B.evalPdisk wl wr = L.eval wl wr := by
  sorry

end ConformalBlock
