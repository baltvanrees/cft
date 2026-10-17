import Mathlib
import CFT.CutPlane
import CFT.Blocks_eucl

/-!
# Euclidean Four-Point Functions

This file defines the data of a Euclidean four-point correlation function of identical scalar
primary operators of scaling dimension $\Delta_\phi$, expanded in Euclidean conformal blocks
$G_{\Delta, l}(\rho)$ from `Blocks_eucl.lean` against a nonnegative OPE spectral measure
$\mu(\Delta, l)$ on $\mathbb{R} \times \mathbb{N}$.
-/

open Real Complex Topology Set Metric MeasureTheory
open scoped ComplexConjugate

/-- Evaluation of the Euclidean four-point correlator at $\rho \in \mathbb{C}$ by integrating the
Euclidean conformal blocks $G_{\Delta, l}(\rho)$ against the OPE measure $\mu$:
$$\mathcal{G}_{\text{eucl}}(\rho) = \int G_{\Delta, l}(\rho) \, d\mu(\Delta, l).$$ -/
noncomputable def eval_correlator_eucl {ν : ℝ}
    (blocks : ∀ (Δ : ℝ) (l : ℕ), EuclideanConformalBlock ν Δ l)
    (mu : Measure (ℝ × ℕ)) (ρ : ℂ) : ℝ :=
  ∫ p : ℝ × ℕ, (blocks p.1 p.2).eval ρ ∂mu

/-- Data for a Euclidean four-point function of identical scalars of scaling dimension $\Delta_\phi$
in spacetime dimension $d = 2\nu + 2$. -/
structure EuclideanFourPointData (ν Δ_phi : ℝ) where
  /-- Nonnegative OPE measure over primary scaling dimension $\Delta \in \mathbb{R}$ and spin
  $l \in \mathbb{N}$. -/
  mu_measure : Measure (ℝ × ℕ)

  /-- Family of Euclidean conformal blocks $G_{\Delta, l}$ for each $(\Delta, l)$. -/
  blocks : ∀ (Δ : ℝ) (l : ℕ), EuclideanConformalBlock ν Δ l

  /-- Unitarity bound support: the OPE measure is supported on non-negative twist
  $\tau = \Delta - l \ge 0$. -/
  support_unitary : mu_measure { p : ℝ × ℕ | p.1 < (p.2 : ℝ) } = 0

  /-- Euclidean OPE convergence on the punctured open unit $\rho$-disk $0 < \|\rho\| < 1$. -/
  converges_correlator_eucl : ∀ ρ ∈ ball (0 : ℂ) 1 \ {0},
    Integrable (fun p : ℝ × ℕ => (blocks p.1 p.2).eval ρ) mu_measure

  /-- Euclidean crossing symmetry on the twice-cut plane $z \in \text{CutPlane}$:
  $$\|z\|^{-2\Delta_\phi} \mathcal{G}_{\text{eucl}}(\rho(z)) =
    \|1 - z\|^{-2\Delta_\phi} \mathcal{G}_{\text{eucl}}(\rho(1 - z)).$$ -/
  crossing_correlator_eucl : ∀ z ∈ CutPlane,
    ‖z‖ ^ (-2 * Δ_phi) * eval_correlator_eucl blocks mu_measure (rho z) =
    ‖1 - z‖ ^ (-2 * Δ_phi) * eval_correlator_eucl blocks mu_measure (rho (1 - z))

namespace EuclideanFourPointData

variable {ν Δ_phi : ℝ} (corr : EuclideanFourPointData ν Δ_phi)

/-- The Euclidean four-point correlator as a function of $\rho \in \mathbb{C}$. -/
noncomputable def correlator_eucl (ρ : ℂ) : ℝ :=
  eval_correlator_eucl corr.blocks corr.mu_measure ρ

/-- The Euclidean four-point correlator as a function of the cross-ratio $z \in \text{CutPlane}$. -/
noncomputable def correlator_z (z : ℂ) : ℝ :=
  corr.correlator_eucl (rho z)

end EuclideanFourPointData
