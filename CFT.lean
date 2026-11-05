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
import CFT.Analysis.DominatedHolomorphy
import CFT.Analysis.Vitali
import CFT.Analysis.HermiteMeasure
import CFT.Analysis.TwoConstants
import CFT.Analysis.LaplaceTauberian
import CFT.LightconeBootstrap.MonomialDecomp
import CFT.LightconeBootstrap.Gap
import CFT.LightconeBootstrap.RealLaplaceBound
import CFT.LightconeBootstrap.QuantitativeLargeSpin
import CFT.LightconeBootstrap.Transmute1d
import CFT.LightconeBootstrap.LightconeBlockDecomp
import CFT.LightconeBootstrap.TransmutedRealLaplace
import CFT.LightconeBootstrap.TransmutedEndpointBounds
import CFT.LightconeBootstrap.ExactTransmutedRef
import CFT.LightconeBootstrap.TransmutedCrossing
import CFT.LightconeBootstrap.PrimaryAllTwists
import CFT.Analysis.Karamata2d
import CFT.ConeTauberian.ErdelyiKoberInversion
import CFT.ConeTauberian.Branching2d
import CFT.ConeTauberian.ConeAsymptotics

/-!
# Towards formalizing conformal field theory in Lean 4

This library formalizes the analytic structure of four-point correlation functions of identical
scalar primary operators in reflection-positive conformal field theories in $d \ge 2$ dimensions
($\nu = (d-2)/2 \ge 0$), starting from Euclidean OPE convergence and crossing symmetry and
culminating in both the **quantitative lightcone bootstrap** ($\ell \to \infty$ at fixed twist)
and **quantitative high-energy Tauberian asymptotics** ($\Delta \to \infty$ at fixed
spin-to-dimension ratio $\xi = \ell / \Delta$) for $d$-dimensional primary operators.

## Module Overview

1. **Coordinate Domains & Identity Theorems (`CFT.CutPlane`)**:
   - The twice-cut plane
   $\operatorname{CutPlane} = \mathbb{C} \setminus ((-\infty, 0] \cup [1, \infty))$. CFT correlation
   functions live  on two copies of this set, parametrized by $z_l$ and $z_r$.
   - The familiar radial coordinate map $\rho(z)$ which maps this domain into the unit disk, with
   the right cut to its boundary.
   - The coordinates $(w_l, w_r)$ which are defined through $\rho(z_l) = e^{w_l}$ and similarly for
   $z_r$. These coordinates each live on the left half plane, with
   $\operatorname{UcDisk} = \{\operatorname{Re}(w) < 0\}$. We call it `UcDisk` because
   it is the universal cover of the disk. We also define `UcPdisk` as two copies of `UcDisk`.
   - Some elementary properties of these sets and analytic functions on them.
2. **Gegenbauer Polynomials & Conformal Blocks (`CFT.Gegenbauers`, `CFT.Blocks`, `CFT.Blocks_1d`,
   `CFT.Blocks_pdisk`)**:
   - Gegenbauer polynomials $C_j^\nu$. The extension in `geg_two_var_sum` to the two-variable
     function
     $$
     (ρ_1 ρ_2)^n C_n^{(ν)}\big( (ρ1 / ρ2 + ρ2 / ρ1) / 2 \big)
     $$
     for which we know the series coefficients exactly. The positivity of these coefficients will do
     a lot of the heavy lifting in the analytic continuation to two independent complex
     variables.
   - Euclidean conformal blocks (`ConformalBlock` and canonical `conformalBlock ν Δ l`) as functions
     of a single complex variable $ρ$, of the form
     $$
    G_{\Delta}^{(l)}(\rho) = \sum_{n=0}^{\infty} \|\rho\|^{\Delta + n}
      \sum_{j \in S(l, n)} A_{n, j} C_j^\nu(\cos \arg \rho)\,.
     $$
     with coefficients $A_{n,j}$ whose existence (`exists_conformalBlock`) and measurability
     (`measurable_conformalBlock_A`) are stated as theorems to be discharged from the conformal
     Casimir recursion.
   - The analytic continuation of conformal blocks to `UcPDisk`
     (`ConformalBlock.evalPdisk`) and joint holomorphy (`ConformalBlock.differentiableOn_evalPdisk`)
     on $\operatorname{UcPdisk}$.
   - One-dimensional $SL(2, \mathbb{R})$ collinear conformal blocks (`block1d`). The decomposition
     of higher-dimensional conformal blocks in one-dimensional blocks will be useful for the
     lightcone bootstrap.
3. **Four-Point Functions & Analytic Continuation of Crossing (`CFT.Corr`, `CFT.Corr_pdisk`)**:
   - Euclidean four-point data (`FourPointData`) and the Euclidean correlator in `CFT.Corr`. We
     postulate OPE convergence in Euclidean signature and then prove it in the polydisk
     (`FourPointData.converges_correlator_pdisk`). We also likewise analytically continue
     $s \leftrightarrow t$ crossing symmetry (`FourPointData.crossing_correlator`) from the
     Euclidean section $z_r = \bar{z}_l$ to independent complex variables
     $(z_l, z_r) \in \operatorname{CutPlane} \times \operatorname{CutPlane}$.
     Finally we prove joint holomorphy (`FourPointData.differentiableOn_correlator_pdisk`).
4. **Standalone Complex & Tauberian Analysis (`CFT.Analysis.*`)**:
   - `CFT.Analysis.DominatedHolomorphy`: Cauchy Fréchet derivative and local Lipschitz bounds for
     bounded holomorphic functions, and joint holomorphy of locally dominated parametric integrals
     and series (`CFT.differentiableOn_integral_of_differentiableOn_of_norm_le`,
     `CFT.differentiableOn_tsum_of_differentiableOn_of_norm_le`).
   - `CFT.Analysis.Vitali`: Real-interval Vitali-type convergence theorem on connected open domains
     (`CFT.vitali_porter_real_interval`, `CFT.vitali_porter_ucDisk`).
   - `CFT.Analysis.HermiteMeasure`: Fejér kernel $K(u)$, Fejér–Hermite interpolant $H_\psi$, and
     the bandlimited + quadratic lattice-distance measure estimate on $\mathbb{Z}$
     (`abs_integral_sub_le_of_fourier_bound`).
   - `CFT.Analysis.TwoConstants`: Harmonic measure on a vertical half-strip and Nevanlinna's
     Two-Constants Theorem (`norm_le_two_constants_vertical_strip`,
     `norm_le_midpoint_two_constants`).
   - `CFT.Analysis.LaplaceTauberian`: Non-asymptotic and power-law Laplace-to-$C_c^2$ Tauberian
     theorems on $\mathbb{Z}$ via exponential tilting
     (`abs_integral_sub_le_of_laplaceReal_bound`, `exists_const_abs_integral_sub_le_rpow`).
   - `CFT.Analysis.Karamata2d`: Non-asymptotic and quantitative $O(\Delta^{-\gamma})$ two-variable
     Fourier-Laplace Tauberian theorems on $\mathbb{R}^2$ via bandlimited truncation on
     $[-R, R]^2$ (`abs_integral_sub_le_of_laplace2d_bound`,
     `exists_const_abs_integral_sub_le_rpow_2d`).
5. **Quantitative Lightcone Bootstrap (`CFT.LightconeBootstrap.*`)**:
   - `CFT.LightconeBootstrap.MonomialDecomp`: Monomial four-point data (`MonomialFourPointData`),
     even-spin $\pi$-periodicity, $s$-channel positivity bounds, folded spin-$2k$ Fourier
     projection on $[-\pi/2, \pi/2]$ (`laplaceSpinReal_eq_fourierProjSpin`), and the canonical
     pushforward construction `FourPointData.toMonomialFourPointData` with evaluation theorem
     `FourPointData.toMonomialFourPointData_eval`.
   - `CFT.LightconeBootstrap.Gap`: Twist-gap condition (`MonomialFourPointData.HasTwistGap`),
     universal-cover crossing equation (`MonomialFourPointData.eval_eq_cross`), and $t$-channel
     identity dominance bounds (`MonomialFourPointData.norm_eval_sub_crossIdentity_le`).
   - `CFT.LightconeBootstrap.RealLaplaceBound`: Quantitative $O(K^{-1})$ Euler Gamma and
     mixed-exponent binomial series bounds (`exists_abs_rpow_mul_pochhammerCoeff_sub_inv_gamma_le`,
     `exists_uniform_bound_tsum_pochhammerCoeff_mixed_sub`) and uniform real-axis Laplace error
     bounds on compact negative intervals $[\sigma_-, \sigma_+]$
     (`MonomialFourPointData.exists_uniform_laplaceSpinReal_sub_identity_bounds`,
     `MonomialFourPointData.exists_uniform_laplaceSpinReal_bounds`).
   - `CFT.LightconeBootstrap.QuantitativeLargeSpin`: Main quantitative $O((2k)^{-\gamma})$
     monomial lightcone bootstrap theorems for compactly supported $C^2$ test functions against
     both the exact $t$-channel identity (`FourPointData.exists_const_abs_pairSpin_sub_identity_le`)
     and the universal Gamma limit (`FourPointData.exists_const_abs_pairSpin_sub_universal_le`).
   - `CFT.LightconeBootstrap.Transmute1d`: 1D fractional transmutation operators (`transmuteCore`,
     `transmuteOp`) on $\operatorname{UcDisk}$, half-binomial convolution and partial-fraction
     identities (`sum_halfBinom_mul_halfBinom`, `sum_halfBinom_div_add_eq_pochhammer_div`),
     the core transmutation theorems (`transmuteCore_block1d`, `transmuteOp_block1d`), and the
     non-negative truncated weight (`transmutePosWeight`).
   - `CFT.LightconeBootstrap.LightconeBlockDecomp`: Action of `transmuteOp` on
     `ConformalBlockLightconeLevel` and `ConformalBlockLightcone`,
     `LightconeBlockFourPointData`, its transmuted `MonomialFourPointData` construction
     (`toTransmutedMonomialFourPointData`, `pairSpin_toTransmutedMonomialFourPointData`), and
     the canonical pushforward measures from `FourPointData` (`FourPointData.primaryTwistMeasure`,
     `FourPointData.lightconeMeasure`).
   - `CFT.LightconeBootstrap.TransmutedRealLaplace`: Transmuted universal and 1-term $t$-channel
     identity Laplace transforms (`transmutedUniversalLaplaceReal`,
     `transmutedIdentityLaplaceReal`), their uniform $O(K^{-1})$ proximity
     (`exists_uniform_bound_transmutedIdentityLaplaceReal_sub_universal`), and the leading
     right-moving transmuted crossing factor (`crossFactorTransmuted`).
   - `CFT.LightconeBootstrap.TransmutedEndpointBounds`: Inner-derivative transmutation operator
     (`transmuteOpInner`), its action on constants (`transmuteOpInner_const`) and on all 1D
     conformal blocks $H \ge 0$ (`transmuteOpInner_block1d`, `transmuteOpInner_block1d_of_pos`),
     and the low-$x$ / high-$x$ endpoint cancellation and Cauchy reduction bounds
     (`norm_transmuteOpInner_le_of_split_bounds`, `norm_folded_integral_transmuteOpInner_le`).
   - `CFT.LightconeBootstrap.ExactTransmutedRef`: Exact 3-term inner-transmuted reference
     (`exactTransmutedPochhammer`, `crossIdentityExactTransmuted`,
     `exactTransmutedIdentityPairing`), 1-term and universal pairings (`transmutedIdentityPairing`,
     `transmutedUniversalPairing`), and the inner-derivative crossing interface
     (`HasInnerTransmutedCrossing`,
     `exists_const_abs_muLC_sub_exactIdentity_le_of_innerCrossing`).
   - `CFT.LightconeBootstrap.TransmutedCrossing`: Exact 1D GFF collinear block transmutation
     (`hasSum_gffBlockCoeff_mul_transmuteOpInner_block1d`), untransmuted $t$-channel remainder
     derivative bounds (`exists_low_x_deriv_bounds_tChannelRemainder`,
     `exists_high_x_deriv_bounds_tChannelRemainder`), derivation of `HasInnerTransmutedCrossing`
     from base crossing and collinear block agreement
     (`LightconeBlockFourPointData.hasInnerTransmutedCrossing_of_agreesWithCorrelator`), and the
     unconditional quantitative 1D lightcone-block bootstrap theorems on `FourPointData`
     (`FourPointData.exists_const_abs_lightcone_sub_exactIdentity_le`,
     `FourPointData.exists_const_abs_lightcone_sub_identity_le`,
     `FourPointData.exists_const_abs_lightcone_sub_universal_le`).
   - `CFT.LightconeBootstrap.PrimaryAllTwists`: Normalized subleading collinear block coefficients
     (`normalizedCollinearBlockCoeff`), exact rational transmutation weight ratio
     (`weightShiftRatio_eq_transmuteWeight_div`), collinear block transfer functions
     (`collinearTransferRatio`, `collinearTransferFn`), recursive GFF $d$-dimensional primary
     coefficients and pairing (`gffPrimaryCoeff`, `gffPrimaryPairing`), and finite triangular
     inversion deriving the quantitative lightcone bootstrap for $d$-dimensional primary operators
     at all bounded twists $h \in [-N, N]$ with full exponent
     $0 < \gamma < \min(2 h_{\text{gap}},\, 2\Delta_\phi)$
     (`FourPointData.exists_const_abs_primary_allTwists_sub_gffPrimary_le`,
     `FourPointData.exists_const_abs_primary_unweighted_allTwists_le`).
6. **Quantitative High-Energy Cone Tauberian Bootstrap (`CFT.ConeTauberian.*`)**:
   - `CFT.ConeTauberian.ErdelyiKoberInversion`: Real Euler Beta integral, Weyl / Erdélyi–Kober
     fractional integral eigenfunction identity (`weylIntegralRight_one_sub_rpow`), continuum
     primary spectral density $\rho^{\text{prim}}_{\nu, \Delta_\phi}(u, \xi)$
     (`primaryConeDensity`) and its closed-form Erdélyi–Kober fractional integral representation
     (`primaryConeDensity_eq_weylIntegralRight`), its exact $d \to 2$ branching integral
     (`integral_branchingKernel_mul_primaryConeDensity`), and its full unit-cylinder integral
     (`integral_primaryConeDensity_cylinder`).
   - `CFT.ConeTauberian.Branching2d`: 2D conformal blocks (`block2dChiral`, `block2d`), bilateral
     1D transmutation $\mathcal{L}_0 \otimes \mathcal{L}_0$ (`transmuteOp2d_block2dChiral`,
     `transmuteOp2d_block2d`), Gegenbauer-to-2D spin coefficients (`gegSpinCoeff`), transverse
     shift binomial resummation (`hasSum_transverseShift`), and uniform $O(\Delta^{-1})$ Stirling
     bounds (`exists_abs_rpow_mul_gegSpinCoeff_sub_inv_gamma_sq_le`,
     `exists_abs_rpow_mul_transmuteWeight_nat_sub_one_le`).
   - `CFT.ConeTauberian.ConeAsymptotics`: 2D bilaterally transmuted measures
     (`FourPointData.transmutedMeasure2d`, `transmutedIdentityMeasure2d`), the pure $2 h_{\text{gap}}$
     quantitative bound against the exact universal $t$-channel identity
     (`FourPointData.exists_const_abs_transmuted2d_sub_identity_le`), the quantitative
     $\min(2 h_{\text{gap}} / (4\Delta_\phi + 1), 1)$ smoothed primary bootstrap theorem
     (`FourPointData.exists_const_abs_primaryCone_sub_le`), and cumulative spin-summed
     primary asymptotics (`FourPointData.tendsto_cumulativePrimaryWeight`).
-/
