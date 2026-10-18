/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Balt van Rees
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import CFT.CutPlane
import CFT.Gegenbauers
import CFT.Blocks_1d
import CFT.Blocks

/-!
# Polydisk & Lightcone Conformal Blocks on the Universal Cover (`UcPdisk`)

This file extends conformal blocks from `Blocks.lean` to two independent complex variables
$(w_l, w_r) \in \operatorname{UcPdisk}$ on the universal cover of the punctured polydisk,
where $(\rho_l, \rho_r) = (e^{w_l}, e^{w_r})$ with $\operatorname{Re}(w_l) < 0$ and
$\operatorname{Re}(w_r) < 0$.

1. **Polydisk continuation (`ConformalBlock.evalPdisk`)**:
   Using `geg_two_var_conj` from `Gegenbauers.lean`,
   $$\|\rho\|^j C_j^\nu(\cos(\arg \rho)) = \sum_{a=0}^{j} c_{j, a}^\nu \rho^a \bar{\rho}^{j - a},$$
   each level $n$ of a `ConformalBlock` extends holomorphically to $(w_l, w_r) \in
   \operatorname{UcPdisk}$ by replacing $(\rho, \bar{\rho})$ with $(e^{w_l}, e^{w_r})$.

2. **Lightcone decomposition (`ConformalBlockLightcone`)**:
   Expanding at fixed left-moving twist level $m \in \mathbb{N}$ gives
   $$G_{\Delta, l}(e^{w_l}, e^{w_r}) =
     \sum_{m=0}^{\infty} e^{((\Delta - l)/2 + m) w_l} g_m(w_r),$$
   where $g_0(w_r)$ is proportional to a single one-dimensional conformal block
   $k_{(\Delta + l)/2}(e^{w_r})$ (`block1d` from `Blocks_1d.lean`) and each $g_m(w_r)$ ($m > 0$) is
   a finite linear combination of 1D conformal blocks with non-negative coefficients.
-/

open Real Complex Topology Set Metric Polynomial
open scoped ComplexConjugate

/-!
## Polydisk Continuation of `ConformalBlock`
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

/-- On the Euclidean section $w_r = \bar{w}$, `evalTermPdisk` agrees with the Euclidean level
contribution `evalTerm` at $\rho = e^w$. -/
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
summed over descendant levels $n \in \mathbb{N}$. -/
noncomputable def evalPdisk (wl wr : ℂ) : ℂ :=
  ∑' n : ℕ, (B.level n).evalTermPdisk ν Δ wl wr

/-- On the Euclidean section $w_r = \bar{w}$, `B.evalPdisk` agrees with the Euclidean block
`B.eval` at $\rho = e^w$. -/
theorem evalPdisk_conj_eq_eval (hν : 0 ≤ ν) (w : ℂ) :
    B.evalPdisk w (conj w) = (B.eval (Complex.exp w) : ℂ) := by
  dsimp [evalPdisk, eval]
  rw [Complex.ofReal_tsum]
  exact tsum_congr fun n => (B.level n).evalTermPdisk_conj hν Δ w

/-- For $z \in \text{CutPlane}$, `B.evalPdisk` at $(\operatorname{logRho}(z),
\overline{\operatorname{logRho}(z)})$ agrees with the Euclidean block `B.eval (rho z)`. -/
theorem evalPdisk_logRho_conj (hν : 0 ≤ ν) {z : ℂ} (hz : z ∈ CutPlane) :
    B.evalPdisk (logRho z) (conj (logRho z)) = (B.eval (rho z) : ℂ) := by
  rw [B.evalPdisk_conj_eq_eval hν (logRho z), exp_logRho hz]

/-- Triangle inequality bound for `lvl.evalTermPdisk` on $\operatorname{UcPdisk}$ in terms of the
Euclidean level contribution evaluated on the positive real $\rho$-axis at
$r = e^{\max(\operatorname{Re}(w_l), \operatorname{Re}(w_r))} \in (0, 1)$. -/
theorem _root_.ConformalBlockLevel.norm_evalTermPdisk_le_evalTerm {l n : ℕ}
    (lvl : ConformalBlockLevel l n) (hν : 0 ≤ ν) (hΔ : (l : ℝ) ≤ Δ)
    {wl wr : ℂ} (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) :
    ‖lvl.evalTermPdisk ν Δ wl wr‖ ≤
      lvl.evalTerm ν Δ (Real.exp (max wl.re wr.re) : ℂ) := by
  dsimp [ConformalBlockLevel.evalTermPdisk, ConformalBlockLevel.evalTerm,
    ConformalBlockLevel.evalAngular, evalGegenbauer, cosArg]
  set r : ℝ := Real.exp (max wl.re wr.re)
  have hr_pos : 0 < r := Real.exp_pos _
  have hr_lt1 : r < 1 := Real.exp_lt_one_iff.mpr (max_lt hwl hwr)
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
        Real.exp ((Δ + (n : ℝ) - (j : ℝ)) / 2 * max wl.re wr.re) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_max_left wl.re wr.re) h_exp_nonneg)
  have h_exp_wr :
      Real.exp ((Δ + (n : ℝ) - (j : ℝ)) / 2 * wr.re) ≤
        Real.exp ((Δ + (n : ℝ) - (j : ℝ)) / 2 * max wl.re wr.re) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_max_right wl.re wr.re) h_exp_nonneg)
  have h_geg1 :
      ‖gegenbauer.geg_two_var_sum (ν : ℂ) (Complex.exp wl) (Complex.exp wr) j‖ ≤
        r ^ j * ((gegenbauer (ν : ℂ) j).eval 1).re := by
    have h1 := gegenbauer.norm_geg_two_var_sum_le ν hν (Complex.exp wl) (Complex.exp wr) j
    have h2 := gegenbauer.geg_two_var_sum_le_max_R ν hν
      ‖Complex.exp wl‖ ‖Complex.exp wr‖ (norm_nonneg _) (norm_nonneg _) j
    have h_max_norm : max ‖Complex.exp wl‖ ‖Complex.exp wr‖ = r := by
      rw [Complex.norm_exp, Complex.norm_exp, ← Real.exp_monotone.map_max]
    have h_geg_one :
        (gegenbauer.geg_two_var_sum (ν : ℂ) 1 1 j).re = ((gegenbauer (ν : ℂ) j).eval 1).re := by
      have h_conj := (gegenbauer.geg_two_var_conj (ν : ℂ) 1 j).symm
      simp only [norm_one, ofReal_one, one_pow, one_mul, arg_one, Real.cos_zero, map_one] at h_conj
      exact congrArg Complex.re h_conj
    rw [h_max_norm, h_geg_one] at h2
    exact h1.trans h2
  have h_exp_r :
      Real.exp ((Δ + (n : ℝ) - (j : ℝ)) / 2 * max wl.re wr.re) *
        Real.exp ((Δ + (n : ℝ) - (j : ℝ)) / 2 * max wl.re wr.re) * r ^ j =
      r ^ (Δ + (n : ℝ)) := by
    rw [← Real.exp_add]
    have h_sum :
        (Δ + (n : ℝ) - (j : ℝ)) / 2 * max wl.re wr.re +
          (Δ + (n : ℝ) - (j : ℝ)) / 2 * max wl.re wr.re =
        max wl.re wr.re * (Δ + (n : ℝ) - (j : ℝ)) := by ring
    rw [h_sum, Real.exp_mul, ← Real.rpow_natCast r j, ← Real.rpow_add hr_pos]
    congr 1
    ring
  calc
    lvl.A j * Real.exp ((Δ + (n : ℝ) - (j : ℝ)) / 2 * wl.re) *
        Real.exp ((Δ + (n : ℝ) - (j : ℝ)) / 2 * wr.re) *
        ‖gegenbauer.geg_two_var_sum (ν : ℂ) (Complex.exp wl) (Complex.exp wr) j‖
      ≤ lvl.A j * Real.exp ((Δ + (n : ℝ) - (j : ℝ)) / 2 * max wl.re wr.re) *
          Real.exp ((Δ + (n : ℝ) - (j : ℝ)) / 2 * max wl.re wr.re) *
          (r ^ j * ((gegenbauer (ν : ℂ) j).eval 1).re) := by
        have h_prod1 :
            lvl.A j * Real.exp ((Δ + (n : ℝ) - (j : ℝ)) / 2 * wl.re) ≤
              lvl.A j * Real.exp ((Δ + (n : ℝ) - (j : ℝ)) / 2 * max wl.re wr.re) :=
          mul_le_mul_of_nonneg_left h_exp_wl h_A_nonneg
        have h_prod2 :
            lvl.A j * Real.exp ((Δ + (n : ℝ) - (j : ℝ)) / 2 * wl.re) *
                Real.exp ((Δ + (n : ℝ) - (j : ℝ)) / 2 * wr.re) ≤
              lvl.A j * Real.exp ((Δ + (n : ℝ) - (j : ℝ)) / 2 * max wl.re wr.re) *
                Real.exp ((Δ + (n : ℝ) - (j : ℝ)) / 2 * max wl.re wr.re) :=
          mul_le_mul h_prod1 h_exp_wr (Real.exp_pos _).le (by positivity)
        exact mul_le_mul h_prod2 h_geg1 (norm_nonneg _) (by positivity)
    _ = lvl.A j *
          (Real.exp ((Δ + (n : ℝ) - (j : ℝ)) / 2 * max wl.re wr.re) *
            Real.exp ((Δ + (n : ℝ) - (j : ℝ)) / 2 * max wl.re wr.re) * r ^ j) *
          ((gegenbauer (ν : ℂ) j).eval 1).re := by ring
    _ = r ^ (Δ + (n : ℝ)) * (lvl.A j * ((gegenbauer (ν : ℂ) j).eval 1).re) := by
        rw [h_exp_r]
        ring

/-- Triangle inequality bound for `B.evalPdisk` on $\operatorname{UcPdisk}$ in terms of the
Euclidean conformal block evaluated on the positive real $\rho$-axis at
$r = e^{\max(\operatorname{Re}(w_l), \operatorname{Re}(w_r))} \in (0, 1)$. -/
theorem norm_evalPdisk_le_eval (hν : 0 ≤ ν) (hΔ : (l : ℝ) ≤ Δ) {wl wr : ℂ}
    (hwl : wl ∈ UcDisk) (hwr : wr ∈ UcDisk) :
    ‖B.evalPdisk wl wr‖ ≤ B.eval (Real.exp (max wl.re wr.re) : ℂ) := by
  dsimp [evalPdisk, eval]
  set r : ℝ := Real.exp (max wl.re wr.re)
  have hr_pos : 0 < r := Real.exp_pos _
  have hr_lt1 : r < 1 := Real.exp_lt_one_iff.mpr (max_lt hwl hwr)
  have hr_mem : r ∈ Ioo (0 : ℝ) 1 := ⟨hr_pos, hr_lt1⟩
  have h_radial_eq : ∀ n : ℕ,
      (B.level n).evalTerm ν Δ (r : ℂ) = r ^ (Δ + (n : ℝ)) * (B.level n).evalAngular ν 1 := by
    intro n
    dsimp [ConformalBlockLevel.evalTerm, cosArg]
    rw [Complex.norm_real, Real.norm_of_nonneg hr_pos.le,
      Complex.arg_ofReal_of_nonneg hr_pos.le, Real.cos_zero]
  have h_sum_rhs : Summable (fun n : ℕ => (B.level n).evalTerm ν Δ (r : ℂ)) := by
    simp_rw [h_radial_eq]
    exact B.summable_radial r hr_mem
  have h_term_bound : ∀ n : ℕ,
      ‖(B.level n).evalTermPdisk ν Δ wl wr‖ ≤ (B.level n).evalTerm ν Δ (r : ℂ) :=
    fun n => (B.level n).norm_evalTermPdisk_le_evalTerm hν hΔ hwl hwr
  have h_sum_norm : Summable (fun n : ℕ => ‖(B.level n).evalTermPdisk ν Δ wl wr‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) h_term_bound h_sum_rhs
  exact (norm_tsum_le_tsum_norm h_sum_norm).trans
    (h_sum_norm.tsum_le_tsum h_term_bound h_sum_rhs)

/-- Joint holomorphy of `lvl.evalTermPdisk` on $\mathbb{C} \times \mathbb{C}$. -/
theorem _root_.ConformalBlockLevel.differentiable_evalTermPdisk {l n : ℕ}
    (lvl : ConformalBlockLevel l n) (ν Δ : ℝ) :
    Differentiable ℂ (fun w : ℂ × ℂ => lvl.evalTermPdisk ν Δ w.1 w.2) := by
  dsimp [ConformalBlockLevel.evalTermPdisk, gegenbauer.geg_two_var_sum]
  fun_prop

/-- Joint holomorphy of `B.evalPdisk` on $\operatorname{UcPdisk}$. -/
theorem differentiableOn_evalPdisk (hν : 0 ≤ ν) :
    DifferentiableOn ℂ (fun w : ℂ × ℂ => B.evalPdisk w.1 w.2) UcPdisk := by
  sorry

end ConformalBlock

/-!
## Lightcone Conformal Block Decomposition into 1D Conformal Blocks

In the lightcone expansion on $\operatorname{UcPdisk}$:
$$G_{\Delta, l}(e^{w_l}, e^{w_r}) =
  \sum_{m=0}^{\infty} e^{((\Delta - l)/2 + m) w_l} g_m(w_r),$$
the leading twist function $g_0(w_r)$ is proportional to a single one-dimensional conformal
block $k_{(\Delta + l)/2}(e^{w_r})$ from `Blocks_1d.lean`, while each subleading twist function
$g_m(w_r)$ ($m > 0$) is a finite linear combination of 1D conformal blocks
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
level $m$. -/
theorem exists_conformalBlockLightcone (hν : 0 < ν) (hΔ : (l : ℝ) ≤ Δ) :
    ∃ L : ConformalBlockLightcone Δ l,
      ∀ wl ∈ UcDisk, ∀ wr ∈ UcDisk,
        B.evalPdisk wl wr = L.eval wl wr := by
  sorry

end ConformalBlock
