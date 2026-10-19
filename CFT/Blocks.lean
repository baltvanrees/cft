/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI-generated, edited by Balt van Rees
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import CFT.Gegenbauers

/-!
# Conformal Blocks of identical scalar operators

This file defines data structures capturing the series expansion of a conformal block
$G_{\Delta}^{(l)}$ associated to a primary operator of scaling dimension $\Delta$ and spin $l$:
$$
G_{\Delta}^{(l)}(\rho) = \sum_{n=0}^{\infty} \|\rho\|^{\Delta + n}
  \sum_{j \in S(l, n)} A_{n, j} C_j^\nu(\cos \arg \rho)\,.
$$
The set $S(l,n)$ are the `descendantSpins` defined below. The Gegenbauer polynomials $C_j^\nu$
are imported from `Gegenbauers.lean`. The coefficients $A_{n,j}$ are left implicit for now; we admit
that they are positive and such that the series converges for $\cos \arg \rho = 1$. A future version
of this code should include the recursion relation that they obey and prove rather than postulate
convergencee (called summability in Lean).

In this file the idea is that $ρ ∈ ℂ$ so we work in Euclidean signature. The continuation to
independent complex $(ρ, \bar ρ)$ in the polydisk is done in `Blocks_pdisk.lean`.
-/

open Real Complex Topology Set Metric Polynomial

/-- The Gegenbauer polynomial $C_j^\nu(x)$ are defined as complex polynomials in
`Gegenbauers.lean`. This function evaluates them for real arguments on the real numbers.
-/
noncomputable def evalGegenbauer (ν : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  ((gegenbauer (ν : ℂ) j).eval (x : ℂ)).re

/-- The cosine of the argument of $\rho \in \mathbb{C}$, i.e.
$\cos(\arg \rho) = \operatorname{Re}(\rho) / \|\rho\|$. -/
noncomputable def cosArg (ρ : ℂ) : ℝ :=
  Real.cos ρ.arg

/-- The finite set $S(l,n)$ of allowed spins $j$ at descendant level $n$ for a primary of spin $l$:
$$j \in \{l + n, l + n - 2, \dots, \max(l - n, (l + n) \bmod 2)\} \equiv S(l,n).$$
Note that `max (l - n) ((l + n) % 2) = l - n` when `l ≥ n` (since the parity matches), and equals
`0` automatically when `l < n` because we work in `ℕ` which does not contain negative numbers. -/
def descendantSpins (l n : ℕ) : Finset ℕ :=
  (Finset.Icc (l - n) (l + n)).filter (fun j => j % 2 = (l + n) % 2)

@[simp]
lemma mem_descendantSpins {l n j : ℕ} :
    j ∈ descendantSpins l n ↔ l - n ≤ j ∧ j ≤ l + n ∧ j % 2 = (l + n) % 2 := by
  simp [descendantSpins, and_assoc]

/-- Data for a single descendant level $n$ in the conformal multiplet of spin $l$.
Captures the finite sum over allowed spins $j \in S(l, n)$. -/
structure ConformalBlockLevel (l n : ℕ) where
  /-- The coefficients $A_{n, j}$ at level $n$. -/
  A : ℕ → ℝ
  /-- Positivity of the coefficients: $A_{n, j} \ge 0$. -/
  A_nonneg : ∀ j ∈ descendantSpins l n, 0 ≤ A j
  /-- Coefficients vanish outside the allowed spins at level $n$. -/
  A_support : ∀ j ∉ descendantSpins l n, A j = 0

namespace ConformalBlockLevel

variable {l n : ℕ} (lvl : ConformalBlockLevel l n)

/-- The finite angular sum at level $n$:
$$\sum_{j \in S(l, n)} A_{n, j} C_j^\nu(x)$$
where $x = \cos \theta$. -/
noncomputable def evalAngular (ν : ℝ) (x : ℝ) : ℝ :=
  ∑ j ∈ descendantSpins l n, lvl.A j * evalGegenbauer ν j x

/-- The full contribution of level $n$ at $\rho \in \mathbb{C}$ for a primary of dimension $\Delta$:
$$\|\rho\|^{\Delta + n} \sum_{j \in S(l,n)} A_{n, j} C_j^\nu(\cos \arg ρ).$$ -/
noncomputable def evalTerm (ν Δ : ℝ) (ρ : ℂ) : ℝ :=
  ‖ρ‖ ^ (Δ + (n : ℝ)) * lvl.evalAngular ν (cosArg ρ)

end ConformalBlockLevel

/-- Data for the full conformal block $G_{\Delta}^{(l)}$ of scaling dimension $\Delta$ and spin $l$
(with spacetime parameter $\nu = (d - 2) / 2$). Captures the infinite sum over descendant levels
$n \in \mathbb{N}$ of the finite spin sums. -/
structure ConformalBlock (ν Δ : ℝ) (l : ℕ) where
  /-- The descendant data at each level $n \in \mathbb{N}$. -/
  level : ∀ n : ℕ, ConformalBlockLevel l n
  /-- Normalization of the primary operator contribution at $n = 0, j = l$. -/
  norm_primary : (level 0).A l = 1
  /-- For (pairwise) equal external dimensions, the $\rho$-expansion only contains even descendant
  levels $n$, reflecting
  $G_{\Delta}^{(l)}(-\rho) = (-1)^l G_{\Delta}^{(l)}(\rho)$. -/
  A_odd_level : ∀ n : ℕ, Odd n → ∀ j : ℕ, (level n).A j = 0
  /-- Radial summability of the block expansion on the unit disk $ρ \in (0, 1)$, so
  $\cos \arg ρ = 1$. -/
  summable_radial : ∀ r ∈ Ioo (0 : ℝ) 1,
    Summable (fun n : ℕ => r ^ (Δ + (n : ℝ)) * (level n).evalAngular ν 1)

namespace ConformalBlock

variable {ν Δ : ℝ} {l : ℕ} (B : ConformalBlock ν Δ l)

/-- Convenience accessor for the coefficient $A_{n, j}$. -/
def A (n j : ℕ) : ℝ :=
  (B.level n).A j

/-- Evaluation of the Euclidean conformal block $G_{\Delta}^{(l)}(\rho)$ as an infinite sum over $n$
and a finite sum over $j \in S(l,n)$ which are the `descendantSpins`:
$$G_{\Delta}^{(l)}(\rho) = \sum_{n=0}^{\infty} \|\rho\|^{\Delta + n}
  \sum_{j \in S(l, n)} A_{n, j} C_j^\nu(\cos \theta).$$ -/
noncomputable def eval (ρ : ℂ) : ℝ :=
  ∑' n : ℕ, (B.level n).evalTerm ν Δ ρ

end ConformalBlock
