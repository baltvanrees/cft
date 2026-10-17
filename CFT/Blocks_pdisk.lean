/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Balt van Rees
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import CFT.Gegenbauers
import CFT.Blocks

/-!
# Polydisk & Amputated Conformal Blocks

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
Factoring out the leading twist prefactor $\rho_l^{(\Delta - l)/2} \rho_r^{(\Delta - l)/2}$ yields
an `AmputatedConformalBlock` whose expansion in $(\rho_l, \rho_r)$ involves only non-negative
integer powers $(k_l, k_r) \in \mathbb{N} \times \mathbb{N}$.
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

/-- An amputated conformal block in the $(\rho_l, \rho_r)$ polydisk for a primary of scaling
dimension $\Delta$ and spin $l$.
After factoring out the twist prefactor $\rho_l^{(\Delta - l)/2} \rho_r^{(\Delta - l)/2}$,
the block is a power series $\sum_{k_l, k_r \in \mathbb{N}} B_{k_l, k_r} \rho_l^{k_l} \rho_r^{k_r}$
with non-negative coefficients supported on $k_l + k_r \ge l$. -/
structure AmputatedConformalBlock (Δ : ℝ) (l : ℕ) where
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

namespace AmputatedConformalBlock

variable {Δ : ℝ} {l : ℕ} (blk : AmputatedConformalBlock Δ l)

/-- A single monomial term of the full conformal block in the $(\rho_l, \rho_r)$ polydisk:
$$B_{k_l, k_r} \, \rho_l^{(\Delta - l)/2 + k_l} \, \rho_r^{(\Delta - l)/2 + k_r}.$$ -/
noncomputable def evalMonomial (ρl ρr : ℂ) (kl kr : ℕ) : ℂ :=
  (blk.B kl kr : ℂ) * ρl ^ (blockExp Δ l kl : ℂ) * ρr ^ (blockExp Δ l kr : ℂ)

/-- Homogeneous polynomial at descendant level $n$ (where $k_l + k_r = l + n$) of the amputated
block:
$$\sum_{k_l = 0}^{l + n} B_{k_l, l + n - k_l} \, \rho_l^{k_l} \, \rho_r^{l + n - k_l}.$$ -/
noncomputable def evalAmputatedLevel (n : ℕ) (ρl ρr : ℂ) : ℂ :=
  ∑ kl ∈ Finset.range (l + n + 1),
    (blk.B kl (l + n - kl) : ℂ) * ρl ^ kl * ρr ^ (l + n - kl)

/-- Full polydisk contribution at descendant level $n$:
$$\rho_l^{(\Delta - l)/2} \rho_r^{(\Delta - l)/2}
  \sum_{k_l = 0}^{l + n} B_{k_l, l + n - k_l} \, \rho_l^{k_l} \, \rho_r^{l + n - k_l}.$$ -/
noncomputable def evalLevel (n : ℕ) (ρl ρr : ℂ) : ℂ :=
  ρl ^ (((Δ - (l : ℝ)) / 2 : ℝ) : ℂ) * ρr ^ (((Δ - (l : ℝ)) / 2 : ℝ) : ℂ) *
    blk.evalAmputatedLevel n ρl ρr

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

end AmputatedConformalBlock

/-!
## Constructing Polydisk Blocks from `ConformalBlock`
-/

namespace ConformalBlockLevel

variable {l n : ℕ} (lvl : ConformalBlockLevel l n)

/-- Coefficient of $\rho_l^{k_l} \rho_r^{k_r}$ (with $k_l + k_r = l + n$) arising from level $n$
of a conformal block:
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
