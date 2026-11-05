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
canonical conformal blocks $G_{\Delta, l}(\rho)$ against a given OPE measure $\mu$:
$$\mathcal{G}_{\text{eucl}}(\rho) = \int G_{\Delta, l}(\rho) \, d\mu(\Delta, l).$$ -/
noncomputable def eval_correlator_eucl (ν : ℝ)
    (mu : Measure (ℝ × ℕ)) (ρ : ℂ) : ℝ :=
  ∫ p : ℝ × ℕ, (conformalBlock ν p.1 p.2).eval ρ ∂mu

/-- OPE data and Euclidean axioms for a four-point function of identical scalars of scaling
dimension $\Delta_\phi$ in spacetime dimension $d = 2\nu + 2$. -/
structure FourPointData (ν Δ_phi : ℝ) where
  /-- Nonnegative OPE measure over primary scaling dimension $\Delta \in \mathbb{R}$ and spin
  $l \in \mathbb{N}$. -/
  mu_measure : Measure (ℝ × ℕ)

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
    Integrable (fun p : ℝ × ℕ => (conformalBlock ν p.1 p.2).eval ρ) mu_measure

  /-- Euclidean crossing symmetry:
$$
\|z\|^{-2\Delta_\phi} \mathcal{G}_{\text{eucl}}(\rho(z)) =
  \|1 - z\|^{-2\Delta_\phi} \mathcal{G}_{\text{eucl}}(\rho(1 - z)).
$$
  We take this to hold when $z \in \text{CutPlane}$, which in turn is defined
  in `CutPlane.lean` to be the entire complex plane minus the two real segments
  $(-∞,0]$ and $[1, ∞)$.
  -/
  crossing_correlator_eucl : ∀ z ∈ CutPlane,
    ‖z‖ ^ (-2 * Δ_phi) * eval_correlator_eucl ν mu_measure (rho z) =
    ‖1 - z‖ ^ (-2 * Δ_phi) * eval_correlator_eucl ν mu_measure (rho (1 - z))

namespace FourPointData

variable {ν Δ_phi : ℝ} (corr : FourPointData ν Δ_phi)

/-- The Euclidean four-point correlator as a function of $\rho \in \mathbb{C}$. Of course
we only have defined the `Integrable` property for $0 < \|\rho\| < 1$ so outside this
region we get a junk value. -/
noncomputable def correlator_eucl (ρ : ℂ) : ℝ :=
  eval_correlator_eucl ν corr.mu_measure ρ

/-- The Euclidean four-point correlator as a function of the cross-ratio $z \in \text{CutPlane}$.
We prove in `CutPlane.lean` that this domain maps into the unit $\rho$ disk.
-/
noncomputable def correlator_z (z : ℂ) : ℝ :=
  corr.correlator_eucl (rho z)

/-- A four-point correlator `corr : FourPointData ν Δ_phi` has a **primary twist gap**
$h_{\mathrm{gap}} > 0$ above the unit-normalized identity operator $(\Delta, l) = (0, 0)$ if:
1. $h_{\mathrm{gap}} > 0$,
2. $\mu(\{(0, 0)\}) = 1$ (unit-normalized identity primary), and
3. $\mu(\{(\Delta, l) \ne (0, 0) \mid (\Delta - l)/2 < h_{\mathrm{gap}}\}) = 0$ (every
   non-identity primary has half-twist $h = (\Delta - l)/2 \ge h_{\mathrm{gap}}$). -/
structure HasTwistGap (h_gap : ℝ) : Prop where
  /-- Positivity of the primary twist gap $h_{\mathrm{gap}} > 0$. -/
  h_gap_pos : 0 < h_gap
  /-- Unit normalization of the identity primary $(\Delta, l) = (0, 0)$. -/
  mu_identity : corr.mu_measure {((0 : ℝ), (0 : ℕ))} = 1
  /-- Every non-identity primary $(\Delta, l) \ne (0, 0)$ has half-twist
  $(\Delta - l) / 2 \ge h_{\mathrm{gap}}$ almost everywhere. -/
  support_gap :
    corr.mu_measure { p : ℝ × ℕ | p ≠ ((0 : ℝ), (0 : ℕ)) ∧ (p.1 - (p.2 : ℝ)) / 2 < h_gap } = 0

/-- Monotonicity of `HasTwistGap`: any smaller positive gap $0 < h' \le h_{\mathrm{gap}}$ is also
a valid primary twist gap. -/
theorem HasTwistGap.mono {h_gap h' : ℝ} (hgap : corr.HasTwistGap h_gap)
    (hh'_pos : 0 < h') (hh'_le : h' ≤ h_gap) :
    corr.HasTwistGap h' := by
  refine ⟨hh'_pos, hgap.mu_identity, measure_mono_null (fun p hp => ?_) hgap.support_gap⟩
  exact ⟨hp.1, hp.2.trans_le hh'_le⟩

end FourPointData
