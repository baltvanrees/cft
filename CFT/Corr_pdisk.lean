import Mathlib
import CFT.CutPlane
import CFT.Blocks_pdisk
import CFT.Corr_eucl

/-!
# Polydisk Four-Point Functions & Analytic Continuation

This file defines the four-point correlation function in the $(\rho_l, \rho_r)$ polydisk and on
$\text{CutPlane} \times \text{CutPlane}$, obtained by integrating the polydisk conformal blocks
from `Blocks_pdisk.lean` against the OPE measure $\mu(\Delta, l)$ on $\mathbb{R} \times \mathbb{N}$.
-/

open Real Complex Topology Set Metric MeasureTheory
open scoped ComplexConjugate

/-- Evaluation of the polydisk four-point correlator from a family of `EuclideanConformalBlock`s
extended to the polydisk $(\rho_l, \rho_r)$ and integrated against the OPE measure $\mu$:
$$\mathcal{G}_{\text{pdisk}}(\rho_l, \rho_r) =
  \int G_{\Delta, l}^{\text{pdisk}}(\rho_l, \rho_r) \, d\mu(\Delta, l).$$ -/
noncomputable def eval_correlator_pdisk {ν : ℝ}
    (blocks : ∀ (Δ : ℝ) (l : ℕ), EuclideanConformalBlock ν Δ l)
    (mu : Measure (ℝ × ℕ)) (ρl ρr : ℂ) : ℂ :=
  ∫ p : ℝ × ℕ, (blocks p.1 p.2).evalPdisk ρl ρr ∂mu

namespace EuclideanFourPointData

variable {ν Δ_phi : ℝ} (corr : EuclideanFourPointData ν Δ_phi)

/-- The four-point correlator continued to the $(\rho_l, \rho_r)$ polydisk using the same OPE
measure `corr.mu_measure` and the polydisk continuation of `corr.blocks`. -/
noncomputable def correlator_pdisk (ρl ρr : ℂ) : ℂ :=
  eval_correlator_pdisk corr.blocks corr.mu_measure ρl ρr

/-- The physical four-point correlator as a function of independent complex coordinates
$(z_l, z_r) \in \text{CutPlane} \times \text{CutPlane}$, mapped into the $\rho$-polydisk via
$(\rho(z_l), \rho(z_r))$. -/
noncomputable def correlator (zl zr : ℂ) : ℂ :=
  corr.correlator_pdisk (rho zl) (rho zr)

/-- Direct-channel side of the crossing equation for independent complex coordinates
$(z_l, z_r) \in \text{CutPlane} \times \text{CutPlane}$:
$$z_l^{-\Delta_\phi} z_r^{-\Delta_\phi} \mathcal{G}(z_l, z_r).$$ -/
noncomputable def crossing_lhs (zl zr : ℂ) : ℂ :=
  zl ^ (- (Δ_phi : ℂ)) * zr ^ (- (Δ_phi : ℂ)) * corr.correlator zl zr

end EuclideanFourPointData

/-- Data for a four-point function in the $(\rho_l, \rho_r)$ polydisk expanded directly in
`AmputatedConformalBlock`s (useful for the lightcone bootstrap where blocks are grouped by twist
$\tau + 2 k_l$). -/
structure PolydiskFourPointData (Δ_phi : ℝ) where
  /-- Nonnegative OPE measure over primary scaling dimension $\Delta \in \mathbb{R}$ and spin
  $l \in \mathbb{N}$. -/
  mu_measure : Measure (ℝ × ℕ)

  /-- Family of amputated polydisk conformal blocks for each $(\Delta, l)$. -/
  blocks : ∀ (Δ : ℝ) (l : ℕ), AmputatedConformalBlock Δ l

  /-- Unitarity bound support: $\Delta - l \ge 0$ a.e. -/
  support_unitary : mu_measure { p : ℝ × ℕ | p.1 < (p.2 : ℝ) } = 0

  /-- Absolute convergence of the polydisk block expansion on the punctured open bidisk. -/
  converges_correlator_pdisk :
    ∀ ρl ∈ ball (0 : ℂ) 1 \ {0}, ∀ ρr ∈ ball (0 : ℂ) 1 \ {0},
      Integrable (fun p : ℝ × ℕ => (blocks p.1 p.2).evalPdisk ρl ρr) mu_measure

  /-- Crossing symmetry for independent complex coordinates
  $(z_l, z_r) \in \text{CutPlane} \times \text{CutPlane}$. -/
  crossing_correlator : ∀ zl ∈ CutPlane, ∀ zr ∈ CutPlane,
    zl ^ (- (Δ_phi : ℂ)) * zr ^ (- (Δ_phi : ℂ)) *
      (∫ p : ℝ × ℕ, (blocks p.1 p.2).evalPdisk (rho zl) (rho zr) ∂mu_measure) =
    (1 - zl) ^ (- (Δ_phi : ℂ)) * (1 - zr) ^ (- (Δ_phi : ℂ)) *
      (∫ p : ℝ × ℕ, (blocks p.1 p.2).evalPdisk (rho (1 - zl)) (rho (1 - zr)) ∂mu_measure)

namespace PolydiskFourPointData

variable {Δ_phi : ℝ} (corr : PolydiskFourPointData Δ_phi)

/-- Evaluation of the polydisk four-point correlator at $(\rho_l, \rho_r)$. -/
noncomputable def correlator_pdisk (ρl ρr : ℂ) : ℂ :=
  ∫ p : ℝ × ℕ, (corr.blocks p.1 p.2).evalPdisk ρl ρr ∂corr.mu_measure

/-- Evaluation of the four-point correlator at external coordinates $(z_l, z_r)$. -/
noncomputable def correlator (zl zr : ℂ) : ℂ :=
  corr.correlator_pdisk (rho zl) (rho zr)

/-- Evaluation of the polydisk four-point correlator using the lightcone block decomposition. -/
noncomputable def correlator_lightcone (ρl ρr : ℂ) : ℂ :=
  ∫ p : ℝ × ℕ, (corr.blocks p.1 p.2).evalLightcone ρl ρr ∂corr.mu_measure

end PolydiskFourPointData

