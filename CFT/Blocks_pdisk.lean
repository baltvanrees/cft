/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Balt van Rees
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import CFT.Gegenbauers
import CFT.Blocks_1d
import CFT.Blocks

/-!
# Polydisk & Lightcone Conformal Blocks

This file extends conformal blocks from `Blocks.lean` to two independent complex
variables $(\rho_l, \rho_r)$ in the polydisk.

Using `geg_two_var_conj` from `Gegenbauers.lean`:
$$\|\rho\|^j C_j^\nu(\cos(\arg \rho)) = \sum_{a=0}^{j} c_{j, a}^\nu \rho^a \bar{\rho}^{j - a}$$
and the parity condition $j \equiv l + n \pmod 2$ with $j \le l + n$ for
$j \in \text{descendantSpins}(l, n)$, every term at descendant level $n$ has left and right
exponents:
$$h_l = \frac{\Delta - l}{2} + k_l, \qquad h_r = \frac{\Delta - l}{2} + k_r,$$
where
$$k_l = \frac{l + n - j}{2} + a \in \mathbb{N}, \qquad
  k_r = \frac{l + n - j}{2} + (j - a) \in \mathbb{N}, \qquad
  k_l + k_r = l + n.$$
This motivates two representations in the $(\rho_l, \rho_r)$ polydisk:
1. `ConformalBlockPdisk`: the double power series in $(k_l, k_r) \in \mathbb{N} \times \mathbb{N}$
   with non-negative coefficients $B_{k_l, k_r} \ge 0$.
2. `ConformalBlockLightcone`: the lightcone expansion
   $\sum_{m=0}^{\infty} \rho_l^{(\Delta - l)/2 + m} g_m(\rho_r)$, where $g_0$ is a single
   one-dimensional conformal block (`block1d` from `Blocks_1d.lean`) and each $g_m$ ($m > 0$) is a
   finite linear combination of 1D conformal blocks with non-negative coefficients.
-/

open Real Complex Topology Set Metric Polynomial
open scoped ComplexConjugate

/-- Real-valued two-variable Gegenbauer coefficient $c_{j, a}^\nu$ from `Gegenbauers.lean`. -/
noncomputable def gegCoeff (ν : ℝ) (j a : ℕ) : ℝ :=
  (gegenbauer.geg_two_var_coeff (ν : ℂ) j a).re

lemma gegCoeff_nonneg {ν : ℝ} (hν : 0 ≤ ν) (j a : ℕ) : 0 ≤ gegCoeff ν j a :=
  (gegenbauer.geg_two_var_coeff_nonneg ν hν j a).1

lemma ofReal_gegCoeff {ν : ℝ} (hν : 0 ≤ ν) (j a : ℕ) :
    (gegCoeff ν j a : ℂ) = gegenbauer.geg_two_var_coeff (ν : ℂ) j a := by
  rcases gegenbauer.geg_two_var_coeff_is_nonneg_real ν hν j a with ⟨r, _, hr⟩
  dsimp [gegCoeff]
  rw [hr, ofReal_re]

/-- Left/right scaling exponent $h(k) = \frac{\Delta - l}{2} + k$. -/
noncomputable def blockExp (Δ : ℝ) (l k : ℕ) : ℝ :=
  (Δ - (l : ℝ)) / 2 + (k : ℝ)

/-- A conformal block in the $(\rho_l, \rho_r)$ polydisk for a primary of scaling dimension $\Delta$
and spin $l$, expanded as a double series
$\sum_{k_l, k_r \in \mathbb{N}} B_{k_l, k_r} \rho_l^{(\Delta - l)/2 + k_l}
  \rho_r^{(\Delta - l)/2 + k_r}$
with non-negative coefficients supported on $k_l + k_r \ge l$. -/
structure ConformalBlockPdisk (Δ : ℝ) (l : ℕ) where
  /-- Coefficient $B_{k_l, k_r}$ of $\rho_l^{(\Delta - l)/2 + k_l} \rho_r^{(\Delta - l)/2 + k_r}$.
  -/
  B : ℕ → ℕ → ℝ
  /-- Non-negativity of the polydisk expansion coefficients. -/
  B_nonneg : ∀ kl kr : ℕ, 0 ≤ B kl kr
  /-- Support condition: all terms have total degree $k_l + k_r \ge l$
  (since $k_l + k_r = l + n$). -/
  B_support : ∀ kl kr : ℕ, kl + kr < l → B kl kr = 0
  /-- Summability on the real unit square $(r_l, r_r) \in (0, 1)^2$. -/
  summable_real : ∀ rl ∈ Ioo (0 : ℝ) 1, ∀ rr ∈ Ioo (0 : ℝ) 1,
    Summable (fun p : ℕ × ℕ =>
      B p.1 p.2 * rl ^ blockExp Δ l p.1 * rr ^ blockExp Δ l p.2)

namespace ConformalBlockPdisk

variable {Δ : ℝ} {l : ℕ} (blk : ConformalBlockPdisk Δ l)

/-- A single monomial term of the conformal block in the $(\rho_l, \rho_r)$ polydisk:
$$B_{k_l, k_r} \, \rho_l^{(\Delta - l)/2 + k_l} \, \rho_r^{(\Delta - l)/2 + k_r}.$$ -/
noncomputable def evalMonomial (ρl ρr : ℂ) (kl kr : ℕ) : ℂ :=
  (blk.B kl kr : ℂ) * ρl ^ (blockExp Δ l kl : ℂ) * ρr ^ (blockExp Δ l kr : ℂ)

/-- Polydisk contribution at descendant level $n$ (where $k_l + k_r = l + n$):
$$\sum_{k_l = 0}^{l + n} B_{k_l, l + n - k_l} \,
  \rho_l^{(\Delta - l)/2 + k_l} \, \rho_r^{(\Delta - l)/2 + l + n - k_l}.$$ -/
noncomputable def evalLevel (n : ℕ) (ρl ρr : ℂ) : ℂ :=
  ∑ kl ∈ Finset.range (l + n + 1), blk.evalMonomial ρl ρr kl (l + n - kl)

/-- Evaluation of the conformal block in the $(\rho_l, \rho_r)$ polydisk, summed over descendant
levels $n \in \mathbb{N}$. -/
noncomputable def evalLevelSum (ρl ρr : ℂ) : ℂ :=
  ∑' n : ℕ, blk.evalLevel n ρl ρr

/-- Evaluation of the conformal block in the $(\rho_l, \rho_r)$ polydisk as a double series over
$(k_l, k_r) \in \mathbb{N} \times \mathbb{N}$. -/
noncomputable def evalPdisk (ρl ρr : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ, blk.evalMonomial ρl ρr p.1 p.2

/-- Collinear / lightcone block at twist level $k_l \in \mathbb{N}$ (corresponding to twist
$\tau + 2 k_l = \Delta - l + 2 k_l$), obtained by summing over all right-moving descendants
$k_r \in \mathbb{N}$:
$$g_{k_l}(\rho_r) = \sum_{k_r = 0}^{\infty} B_{k_l, k_r} \, \rho_r^{(\Delta - l)/2 + k_r}.$$ -/
noncomputable def evalLightconeLevel (kl : ℕ) (ρr : ℂ) : ℂ :=
  ∑' kr : ℕ, (blk.B kl kr : ℂ) * ρr ^ (blockExp Δ l kr : ℂ)

/-- Lightcone conformal block decomposition: outer sum over left twist levels $k_l \in \mathbb{N}$
of $\rho_l^{(\Delta - l)/2 + k_l} g_{k_l}(\rho_r)$. -/
noncomputable def evalLightcone (ρl ρr : ℂ) : ℂ :=
  ∑' kl : ℕ, ρl ^ (blockExp Δ l kl : ℂ) * blk.evalLightconeLevel kl ρr

end ConformalBlockPdisk

/-!
## Constructing Polydisk Blocks from `ConformalBlock`
-/

namespace ConformalBlockLevel

variable {l n : ℕ} (lvl : ConformalBlockLevel l n)

/-- Coefficient of $\rho_l^{(\Delta - l)/2 + k_l} \rho_r^{(\Delta - l)/2 + k_r}$
(with $k_l + k_r = l + n$) arising from level $n$ of a conformal block:
$$B^{(n)}_{k_l, k_r} = \sum_j A_{n, j} \, c_{j, k_l - (l + n - j)/2}^\nu.$$ -/
noncomputable def pdiskCoeff (ν : ℝ) (kl kr : ℕ) : ℝ :=
  if kl + kr = l + n then
    ∑ j ∈ (descendantSpins l n).filter
        (fun j => (l + n - j) / 2 ≤ kl ∧ (l + n - j) / 2 ≤ kr),
      lvl.A j * gegCoeff ν j (kl - (l + n - j) / 2)
  else 0

lemma pdiskCoeff_nonneg {ν : ℝ} (hν : 0 ≤ ν) (kl kr : ℕ) :
    0 ≤ lvl.pdiskCoeff ν kl kr := by
  dsimp [pdiskCoeff]
  split_ifs with h
  · refine Finset.sum_nonneg fun j hj => ?_
    rw [Finset.mem_filter] at hj
    exact mul_nonneg (lvl.A_nonneg j hj.1) (gegCoeff_nonneg hν j _)
  · exact le_rfl

/-- Direct polydisk evaluation of level $n$ using `geg_two_var_sum`:
$$\sum_{j \in \text{descendantSpins}(l, n)} A_{n, j}
  (\rho_l \rho_r)^{\frac{\Delta + n - j}{2}}
  \operatorname{geg\_two\_var\_sum}\ \nu\ \rho_l\ \rho_r\ j.$$ -/
noncomputable def evalTermPdisk (ν Δ : ℝ) (ρl ρr : ℂ) : ℂ :=
  ∑ j ∈ descendantSpins l n,
    (lvl.A j : ℂ) *
      ρl ^ (((Δ + (n : ℝ) - (j : ℝ)) / 2 : ℝ) : ℂ) *
      ρr ^ (((Δ + (n : ℝ) - (j : ℝ)) / 2 : ℝ) : ℂ) *
      gegenbauer.geg_two_var_sum (ν : ℂ) ρl ρr j

end ConformalBlockLevel

namespace ConformalBlock

variable {ν Δ : ℝ} {l : ℕ} (B : ConformalBlock ν Δ l)

/-- Two-variable polydisk coefficient $B_{k_l, k_r}$ associated to a `ConformalBlock`.
Since $k_l + k_r = l + n$, only level $n = k_l + k_r - l$ contributes when $k_l + k_r \ge l$. -/
noncomputable def pdiskCoeff (kl kr : ℕ) : ℝ :=
  if kl + kr < l then 0
  else (B.level (kl + kr - l)).pdiskCoeff ν kl kr

lemma pdiskCoeff_nonneg (hν : 0 ≤ ν) (kl kr : ℕ) : 0 ≤ B.pdiskCoeff kl kr := by
  dsimp [pdiskCoeff]
  split_ifs
  · exact le_rfl
  · exact (B.level (kl + kr - l)).pdiskCoeff_nonneg hν kl kr

lemma pdiskCoeff_support (kl kr : ℕ) (h : kl + kr < l) : B.pdiskCoeff kl kr = 0 := by
  simp [pdiskCoeff, h]

/-- Direct polydisk evaluation of a `ConformalBlock` summed over levels $n \in \mathbb{N}$. -/
noncomputable def evalPdisk (ρl ρr : ℂ) : ℂ :=
  ∑' n : ℕ, (B.level n).evalTermPdisk ν Δ ρl ρr

/-- Collinear / lightcone block at twist level $k_l \in \mathbb{N}$ associated to a
`ConformalBlock`. -/
noncomputable def evalLightconeLevel (kl : ℕ) (ρr : ℂ) : ℂ :=
  ∑' kr : ℕ, (B.pdiskCoeff kl kr : ℂ) * ρr ^ (blockExp Δ l kr : ℂ)

/-- Lightcone conformal block decomposition of a `ConformalBlock`: outer sum over left
twist levels $k_l \in \mathbb{N}$ of $\rho_l^{(\Delta - l)/2 + k_l} g_{k_l}(\rho_r)$. -/
noncomputable def evalLightcone (ρl ρr : ℂ) : ℂ :=
  ∑' kl : ℕ, ρl ^ (blockExp Δ l kl : ℂ) * B.evalLightconeLevel kl ρr

end ConformalBlock

/-!
## Lightcone Conformal Block Decomposition into 1D Conformal Blocks

In the lightcone expansion
$$G_{\Delta, l}(\rho_l, \rho_r) = \sum_{m=0}^{\infty} \rho_l^{(\Delta - l)/2 + m} g_m(\rho_r),$$
the leading twist function $g_0(\rho_r)$ is proportional to a single one-dimensional conformal
block $k_{(\Delta + l)/2}(\rho_r)$ from `Blocks_1d.lean`, while each subleading twist function
$g_m(\rho_r)$ ($m > 0$) is a finite linear combination of 1D conformal blocks
$k_{(\Delta - l)/2 + k_r}(\rho_r)$ with non-negative coefficients.
-/

/-- Data for a single left-moving twist level $m$ in the lightcone expansion of a conformal block.
Captures the right-moving function $g_m(\rho_r)$ as a finite linear combination of 1D conformal
blocks $k_{\bar{h}}(\rho_r)$ with non-negative coefficients. -/
structure ConformalBlockLightconeLevel where
  /-- Finite set of right-moving shift indices $k_r \in \mathbb{N}$ appearing in $g_m(\rho_r)$,
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

/-- Evaluation of the right-moving function $g_m(\rho_r)$ as a finite linear combination of
1D conformal blocks:
$$g_m(\rho_r) = \sum_{k_r \in \text{support}} C_{m, k_r} \,
  k_{(\Delta - l)/2 + k_r}(\rho_r).$$ -/
noncomputable def eval (Δ : ℝ) (l : ℕ) (ρr : ℂ) : ℂ :=
  ∑ kr ∈ lvl.support, (lvl.C kr : ℂ) * block1d (blockExp Δ l kr) ρr

end ConformalBlockLightconeLevel

/-- Lightcone decomposition of a conformal block $G_{\Delta, l}(\rho_l, \rho_r)$ into
one-dimensional conformal blocks:
$$G_{\Delta, l}(\rho_l, \rho_r) = \sum_{m=0}^{\infty} \rho_l^{(\Delta - l)/2 + m} g_m(\rho_r),$$
where $g_0(\rho_r) = C_{0, l} \, k_{(\Delta + l)/2}(\rho_r)$ is a single 1D conformal block and
every $g_m(\rho_r)$ for $m > 0$ is a finite linear combination of 1D conformal blocks with
non-negative coefficients. -/
structure ConformalBlockLightcone (Δ : ℝ) (l : ℕ) where
  /-- Lightcone level data $g_m$ for each left-moving twist level $m \in \mathbb{N}$. -/
  level : ℕ → ConformalBlockLightconeLevel
  /-- Leading twist ($m = 0$) consists of a single 1D conformal block at $k_r = l$
  (weight $\bar{h} = (\Delta + l) / 2$). -/
  support_zero : (level 0).support = {l}
  /-- Positivity of the leading 1D conformal block coefficient $C_{0, l} > 0$. -/
  C_zero_pos : 0 < (level 0).C l
  /-- Summability of the lightcone expansion on the real unit square $(r_l, r_r) \in (0, 1)^2$. -/
  summable_real : ∀ rl ∈ Ioo (0 : ℝ) 1, ∀ rr ∈ Ioo (0 : ℝ) 1,
    Summable (fun m : ℕ =>
      rl ^ blockExp Δ l m * ‖(level m).eval Δ l (rr : ℂ)‖)

namespace ConformalBlockLightcone

variable {Δ : ℝ} {l : ℕ} (L : ConformalBlockLightcone Δ l)

/-- Evaluation of the right-moving function $g_m(\rho_r)$ at twist level $m$. -/
noncomputable def evalLevel (m : ℕ) (ρr : ℂ) : ℂ :=
  (L.level m).eval Δ l ρr

/-- Evaluation of the full conformal block via its lightcone expansion:
$$\sum_{m=0}^{\infty} \rho_l^{(\Delta - l)/2 + m} g_m(\rho_r).$$ -/
noncomputable def eval (ρl ρr : ℂ) : ℂ :=
  ∑' m : ℕ, ρl ^ (blockExp Δ l m : ℂ) * L.evalLevel m ρr

/-- At leading twist $m = 0$, $g_0(\rho_r)$ is a single 1D conformal block of weight
$\bar{h} = (\Delta + l) / 2$. -/
lemma evalLevel_zero (ρr : ℂ) :
    L.evalLevel 0 ρr = ((L.level 0).C l : ℂ) * block1d ((Δ + (l : ℝ)) / 2) ρr := by
  dsimp [evalLevel, ConformalBlockLightconeLevel.eval, blockExp]
  rw [L.support_zero, Finset.sum_singleton]
  congr 2
  ring

end ConformalBlockLightcone

namespace ConformalBlock

variable {ν Δ : ℝ} {l : ℕ} (B : ConformalBlock ν Δ l)

/-- Every conformal block admits a lightcone decomposition into finite non-negative sums of
one-dimensional conformal blocks at each left-moving twist level $m$. -/
theorem exists_conformalBlockLightcone (hν : 0 < ν) (hΔ : (l : ℝ) ≤ Δ) :
    ∃ L : ConformalBlockLightcone Δ l,
      (∀ m : ℕ, ∀ ρr ∈ slitPlane ∩ ball (0 : ℂ) 1,
        B.evalLightconeLevel m ρr = L.evalLevel m ρr) ∧
      (∀ ρl ∈ slitPlane ∩ ball (0 : ℂ) 1, ∀ ρr ∈ slitPlane ∩ ball (0 : ℂ) 1,
        B.evalLightcone ρl ρr = L.eval ρl ρr) := by
  sorry

end ConformalBlock
