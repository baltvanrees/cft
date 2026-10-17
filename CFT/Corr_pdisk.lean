/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Balt van Rees
-/
import CFT.CutPlane
import CFT.Blocks_pdisk
import CFT.Corr

/-!
# Polydisk Four-Point Functions & Analytic Continuation

This file extends `FourPointData` from `Corr.lean` to the $(\rho_l, \rho_r)$ polydisk and to
independent complex coordinates $(z_l, z_r) \in \text{CutPlane} \times \text{CutPlane}$, by
integrating the polydisk-continued conformal blocks from `Blocks_pdisk.lean` against the same OPE
measure `corr.mu_measure`.
-/

open Real Complex Topology Set Metric MeasureTheory
open scoped ComplexConjugate

/-- Evaluation of the polydisk four-point correlator from a family of `ConformalBlock`s
extended to the polydisk $(\rho_l, \rho_r)$ and integrated against the OPE measure $\mu$:
$$\mathcal{G}_{\text{pdisk}}(\rho_l, \rho_r) =
  \int G_{\Delta, l}^{\text{pdisk}}(\rho_l, \rho_r) \, d\mu(\Delta, l).$$ -/
noncomputable def eval_correlator_pdisk {ν : ℝ}
    (blocks : ∀ (Δ : ℝ) (l : ℕ), ConformalBlock ν Δ l)
    (mu : Measure (ℝ × ℕ)) (ρl ρr : ℂ) : ℂ :=
  ∫ p : ℝ × ℕ, (blocks p.1 p.2).evalPdisk ρl ρr ∂mu

namespace FourPointData

variable {ν Δ_phi : ℝ} (corr : FourPointData ν Δ_phi)

/-- The four-point correlator continued to the $(\rho_l, \rho_r)$ polydisk using the OPE
measure `corr.mu_measure` and the polydisk continuation of `corr.blocks`. -/
noncomputable def correlator_pdisk (ρl ρr : ℂ) : ℂ :=
  eval_correlator_pdisk corr.blocks corr.mu_measure ρl ρr

/-- Evaluation of the polydisk four-point correlator using the lightcone block decomposition of
`corr.blocks`. -/
noncomputable def correlator_lightcone (ρl ρr : ℂ) : ℂ :=
  ∫ p : ℝ × ℕ, (corr.blocks p.1 p.2).evalLightcone ρl ρr ∂corr.mu_measure

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

end FourPointData
