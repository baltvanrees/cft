/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI-generated, edited by Balt van Rees
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import CFT.CutPlane
import CFT.Blocks

/-!
# Four-Point Functions of identical scalar operators

This file defines `FourPointData`, capturing the OPE data of a four-point correlation function of
identical scalar primary operators, expanded in conformal blocks $G_{\Delta,l}$ from
`Blocks.lean` against a nonnegative OPE spectral measure
$\mu(\Delta, l)$ on $\mathbb{R} \times \mathbb{N}$.

We also postulate Euclidean OPE convergence, and Euclidean crossing symmetry for which we need the
scaling dimension $Δ_φ$ of the external operator.
-/

open Real Complex Topology Set Metric MeasureTheory
open scoped ComplexConjugate

/-- Evaluation of the Euclidean four-point correlator at $\rho \in \mathbb{C}$ by integrating the
conformal blocks $G_{\Delta, l}(\rho)$ against a given OPE measure $\mu$:
$$\mathcal{G}_{\text{eucl}}(\rho) = \int G_{\Delta, l}(\rho) \, d\mu(\Delta, l).$$ -/
noncomputable def eval_correlator_eucl {ν : ℝ}
    (blocks : ∀ (Δ : ℝ) (l : ℕ), ConformalBlock ν Δ l)
    (mu : Measure (ℝ × ℕ)) (ρ : ℂ) : ℝ :=
  ∫ p : ℝ × ℕ, (blocks p.1 p.2).eval ρ ∂mu

/-- OPE data and Euclidean axioms for a four-point function of identical scalars of scaling
dimension $\Delta_\phi$ in spacetime dimension $d = 2\nu + 2$. -/
structure FourPointData (ν Δ_phi : ℝ) where
  /-- Nonnegative OPE measure over primary scaling dimension $\Delta \in \mathbb{R}$ and spin
  $l \in \mathbb{N}$. -/
  mu_measure : Measure (ℝ × ℕ)

  /-- Family of conformal blocks $G_{\Delta, l}$ for each $(\Delta, l)$. -/
  blocks : ∀ (Δ : ℝ) (l : ℕ), ConformalBlock ν Δ l

  /-- Measurability of the conformal block coefficients $A_{n, j}(\Delta, l)$ across the
  spectrum. -/
  measurable_A : ∀ n j : ℕ, Measurable (fun p : ℝ × ℕ => ((blocks p.1 p.2).level n).A j)

  /-- Unitarity bound support: the OPE measure is supported on non-negative twist
  $\tau = \Delta - l \ge 0$. (We should make this $d$-dependent.) -/
  support_unitary : mu_measure { p : ℝ × ℕ | p.1 < (p.2 : ℝ) } = 0

  /-- Bose symmetry of identical external scalars: the OPE measure is supported on even spins
  $l$. -/
  support_even_spin : mu_measure { p : ℝ × ℕ | Odd p.2 } = 0

  /-- Euclidean OPE convergence on the punctured open unit $\rho$-disk $0 < \|\rho\| < 1$.
  (We could postulate this only for real $ρ$, as we do with the conformal blocks, and then prove
  it holds for complex $ρ$.)
  -/
  converges_correlator_eucl : ∀ ρ ∈ ball (0 : ℂ) 1 \ {0},
    Integrable (fun p : ℝ × ℕ => (blocks p.1 p.2).eval ρ) mu_measure

  /-- Euclidean crossing symmetry:
  $$\|z\|^{-2\Delta_\phi} \mathcal{G}_{\text{eucl}}(\rho(z)) =
    \|1 - z\|^{-2\Delta_\phi} \mathcal{G}_{\text{eucl}}(\rho(1 - z)).$$
  We take this to hold when $z \in \text{CutPlane}$, which in turn is defined
  in `CutPlane.lean` to be the entire complex plane minus the two real segments
  $(-∞,0]$ and $[1, ∞)$.
  -/
  crossing_correlator_eucl : ∀ z ∈ CutPlane,
    ‖z‖ ^ (-2 * Δ_phi) * eval_correlator_eucl blocks mu_measure (rho z) =
    ‖1 - z‖ ^ (-2 * Δ_phi) * eval_correlator_eucl blocks mu_measure (rho (1 - z))

namespace FourPointData

variable {ν Δ_phi : ℝ} (corr : FourPointData ν Δ_phi)

/-- The Euclidean four-point correlator as a function of $\rho \in \mathbb{C}$. Of course
we only have defined the `Integrable` property for $0 < \|\rho\| < 1$ so outside this
region we get a junk value. -/
noncomputable def correlator_eucl (ρ : ℂ) : ℝ :=
  eval_correlator_eucl corr.blocks corr.mu_measure ρ

/-- The Euclidean four-point correlator as a function of the cross-ratio $z \in \text{CutPlane}$.
We prove in `CutPlane.lean` that this domain maps into the unit $\rho$ disk.
-/
noncomputable def correlator_z (z : ℂ) : ℝ :=
  corr.correlator_eucl (rho z)

end FourPointData
