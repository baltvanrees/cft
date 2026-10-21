/-
Copyright (c) 2026 Balt van Rees. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI-generated, edited by Balt van Rees
-/
import CFT.CutPlane
import CFT.Gegenbauers
import CFT.Blocks_1d
import CFT.Blocks
import CFT.Blocks_pdisk
import CFT.Corr
import CFT.Corr_pdisk
import CFT.Vitali
import CFT.LightconeBootstrap.HermiteMeasure
import CFT.LightconeBootstrap.TwoConstants
import CFT.LightconeBootstrap.LaplaceTauberian
import CFT.LightconeBootstrap.MonomialDecomp
import CFT.LightconeBootstrap.Gap
import CFT.LightconeBootstrap.RealLaplaceBound
import CFT.LightconeBootstrap.QuantitativeLargeSpin

/-!
# Towards formalizing conformal field theory in Lean 4

This library formalizes the analytic structure of four-point correlation functions of identical
scalar primary operators in reflection-positive conformal field theories in $d \ge 2$ dimensions
($\nu = (d-2)/2 \ge 0$), starting from Euclidean OPE convergence and crossing symmetry and
culminating in the **monomial lightcone bootstrap**.

## Module Overview

1. **Coordinate Domains & Identity Theorems (`CFT.CutPlane`)**:
   - We define the twice-cut cross-ratio plane $\operatorname{CutPlane} = \mathbb{C} \setminus
     ((-\infty, 0] \cup [1, \infty))$ and radial coordinate $\rho(z)$.
   - The left half-plane $\operatorname{UcDisk} = \{\operatorname{Re}(w) < 0\}$ (universal cover
     of the punctured unit $\rho$-disk via $\rho = e^w$), and its two-variable version
     $\operatorname{UcPdisk} = \operatorname{UcDisk} \times \operatorname{UcDisk}$. Also various
     maps from $z$ to $ρ$ to $w$.
2. **Gegenbauer Polynomials & Conformal Blocks (`CFT.Gegenbauers`, `CFT.Blocks`, `CFT.Blocks_1d`,
   `CFT.Blocks_pdisk`)**:
   - Gegenbauer polynomials $C_j^\nu$. The extension in `geg_two_var_sum` to the two-variable
     function
     $$
     (ρ_1 ρ_2)^n C_n^{(ν)}\big( (ρ1 / ρ2 + ρ2 / ρ1) / 2 \big)
     $$
     and manifest positivity of the coefficients in tis series expansion will do
     a lot of the heavy lifting in the analytic continuation to two independent complex
     variables.
   - Euclidean conformal blocks (`ConformalBlock`) and their analytic continuation
     (`ConformalBlock.evalPdisk`) and joint holomorphy (`ConformalBlock.differentiableOn_evalPdisk`)
     on $\operatorname{UcPdisk}$.
   - One-dimensional $SL(2, \mathbb{R})$ collinear conformal blocks (`block1d`). The decomposition
     of higher-dimensional conformal blocks in one-dimensional blocks will be useful for the
     the lightcone bootstrap.
3. **Four-Point Functions & Analytic Continuation of Crossing (`CFT.Corr`, `CFT.Corr_pdisk`)**:
   - Euclidean four-point data (`FourPointData`) and the Euclidean correlator in `CFT.Corr`. We
     postulate OPE convergence in Euclidean signature and then prove it in the polydisk
     (`FourPointData.converges_correlator_pdisk`). We also likewise analytically continue
     $s \leftrightarrow t$ crossing symmetry (`FourPointData.crossing_correlator`) from the
     Euclidean section $z_r = \bar{z}_l$ to independent complex variables
     $(z_l, z_r) \in \operatorname{CutPlane} \times \operatorname{CutPlane}$.
     Finally we prove joint holomorphy (`FourPointData.differentiableOn_correlator_pdisk`)
4. **Cauchy Derivative Bounds & Real-Interval Vitali Theorem (`CFT.Vitali`)**:
   - Cauchy derivative and local Lipschitz bounds for bounded holomorphic functions, holomorphy of
     locally dominated parametric integrals and series on $\mathbb{C} \times \mathbb{C}$, and the
     real-interval Vitali-type convergence theorem (`CFT.vitali_porter_real_interval`,
     `CFT.vitali_porter_ucDisk`).
5. **Quantitative Monomial Lightcone Bootstrap (`CFT.LightconeBootstrap.*`)**:
   - `CFT.LightconeBootstrap.HermiteMeasure`: Fejér kernel $K(u)$, Fejér–Hermite interpolant
     $H_\psi$, and the bandlimited + quadratic lattice-distance measure estimate on $\mathbb{Z}$
     (`abs_integral_sub_le_of_fourier_bound`, `abs_integral_sub_le_of_fourier_bound_contDiff`).
   - `CFT.LightconeBootstrap.TwoConstants`: Harmonic measure on a vertical half-strip and
     Nevanlinna's Two-Constants Theorem (`norm_le_two_constants_vertical_strip`,
     `norm_le_midpoint_two_constants`).
   - `CFT.LightconeBootstrap.LaplaceTauberian`: Non-asymptotic and power-law Laplace-to-$C_c^2$
     Tauberian theorems on $\mathbb{Z}$ via exponential tilting
     (`abs_integral_sub_le_of_laplaceReal_bound`, `exists_const_abs_integral_sub_le_rpow`).
   - `CFT.LightconeBootstrap.MonomialDecomp`: Monomial four-point data (`MonomialFourPointData`),
     even-spin $\pi$-periodicity, $s$-channel positivity bounds, folded spin-$2k$ Fourier
     projection on $[-\pi/2, \pi/2]$ (`laplaceSpinReal_eq_fourierProjSpin`), and the canonical
     pushforward construction `FourPointData.toMonomialFourPointData` with evaluation theorem
     `FourPointData.toMonomialFourPointData_eval`.
   - `CFT.LightconeBootstrap.Gap`: Twist-gap condition (`MonomialFourPointData.HasTwistGap`),
     universal-cover crossing equation (`MonomialFourPointData.eval_eq_cross`), and $t$-channel
     identity dominance bounds (`MonomialFourPointData.norm_eval_sub_crossIdentity_le`).
   - `CFT.LightconeBootstrap.RealLaplaceBound`: Quantitative $O(K^{-1})$ Euler Gamma and binomial
     series bounds (`exists_abs_rpow_mul_pochhammerCoeff_sub_inv_gamma_le`) and uniform real-axis
     Laplace error bounds on compact negative intervals $[\sigma_-, \sigma_+]$
     (`MonomialFourPointData.exists_uniform_laplaceSpinReal_bounds`).
   - `CFT.LightconeBootstrap.QuantitativeLargeSpin`: Main quantitative $O((2k)^{-\gamma})$
     monomial lightcone bootstrap theorems for compactly supported $C^2$ test functions
     (`MonomialFourPointData.exists_const_abs_pairSpin_sub_universal_le`,
     `MonomialFourPointData.exists_const_abs_pairSpin_sub_universal_le_contDiff`,
     `FourPointData.exists_const_abs_pairSpin_sub_universal_le`). TODO: upgrade documentation.
-/


-- ## Repository Structure and Current Milestones

-- A somewhat more detailed guide is maintained in [PLAN.md](PLAN.md) and in [CFT/MonomialBootstrap/PLAN.md](CFT/MonomialBootstrap/PLAN.md). See also the accompanying LaTeX note [doc/monomial_bootstrap.tex](doc/monomial_bootstrap.tex).

-- - **Complex Geometry & Coordinate Domains ([`CFT/CutPlane.lean`](CFT/CutPlane.lean))**:
--   Defines the twice-cut cross-ratio plane $\operatorname{CutPlane} = \mathbb{C} \setminus ((-\infty, 0] \cup [1, \infty))$, the radial coordinate $\rho(z)$, the left half-plane $\operatorname{UcDisk} = \{\operatorname{Re}(w) < 0\}$ (universal cover of the punctured unit $\rho$-disk via $\rho = e^w$), the polydisk cover $\operatorname{UcPdisk} = \operatorname{UcDisk} \times \operatorname{UcDisk}$, and real-interval identity theorems.
-- - **Gegenbauer Polynomials & Conformal Blocks ([`CFT/Gegenbauers.lean`](CFT/Gegenbauers.lean), [`CFT/Blocks.lean`](CFT/Blocks.lean), [`CFT/Blocks_1d.lean`](CFT/Blocks_1d.lean), [`CFT/Blocks_pdisk.lean`](CFT/Blocks_pdisk.lean))**:
--   Constructs the Gegenbauer polynomials $C_j^\nu$, proves the non-negativity of their two-variable binomial expansion coefficients for $\nu \ge 0$, defines Euclidean conformal blocks $G_{\Delta, l}(\rho)$, and analytically continues them to holomorphic functions on $\operatorname{UcPdisk}$.
-- - **Four-Point Functions & Analytic Continuation of Crossing Symmetry ([`CFT/Corr.lean`](CFT/Corr.lean), [`CFT/Corr_pdisk.lean`](CFT/Corr_pdisk.lean))**:
--   Defines Euclidean four-point correlation functions (`FourPointData`), proves convergence and joint holomorphy of their analytic continuation on $\operatorname{UcPdisk}$, and analytically continues $s \leftrightarrow t$ crossing symmetry from the Euclidean section $z_r = \bar{z}_l$ to independent complex variables $(z_l, z_r) \in \operatorname{CutPlane} \times \operatorname{CutPlane}$.
-- - **Cauchy Fréchet Derivative Bounds & Vitali-Type Convergence ([`CFT/Vitali.lean`](CFT/Vitali.lean))**:
--   Establishes Cauchy derivative and local Lipschitz bounds for bounded holomorphic functions, holomorphy of locally dominated parametric integrals and series on $\mathbb{C} \times \mathbb{C}$, and a real-interval Vitali-type convergence theorem on connected open domains (bypassing Montel's theorem via Tychonoff compactness in the pointwise product topology).
-- - **Monomial Lightcone Bootstrap ([`CFT/MonomialBootstrap/`](CFT/MonomialBootstrap/))**:
--   Constructs the canonical monomial decomposition `FourPointData.toMonomialFourPointData` ([`MonomialDecomp.lean`](CFT/MonomialBootstrap/MonomialDecomp.lean)) and proves the universal large-spin asymptotics of the spin-$2k$ spectral measure $\mu_{2k}$ in any crossing-symmetric theory with a twist gap ([`FourierProj.lean`](CFT/MonomialBootstrap/FourierProj.lean), [`Gap.lean`](CFT/MonomialBootstrap/Gap.lean), [`IdentityProj.lean`](CFT/MonomialBootstrap/IdentityProj.lean), [`LargeSpin.lean`](CFT/MonomialBootstrap/LargeSpin.lean)):
--   $$\lim_{k \to \infty} (2k)^{1 - 2\Delta_\phi} \int_{\mathbb{R}} \varphi(h) \, d\mu_{2k}(h) = \frac{2 \cdot 4^{2\Delta_\phi}}{\Gamma(2\Delta_\phi)} \sum_{n=0}^{\infty} \frac{(2\Delta_\phi)_n}{n!} \, \varphi(\Delta_\phi + n).$$
