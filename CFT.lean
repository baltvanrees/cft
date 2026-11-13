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
import CFT.Analysis.HermiteMeasure
import CFT.Analysis.TwoConstants
import CFT.Analysis.LaplaceTauberian
import CFT.LightconeBootstrap.Monomial.Decomp
import CFT.LightconeBootstrap.Monomial.TwistGap
import CFT.LightconeBootstrap.Monomial.LaplaceBound
import CFT.LightconeBootstrap.Monomial.ReferencePairing
import CFT.LightconeBootstrap.MonomialBootstrap
import CFT.LightconeBootstrap.LightconeBlock.Transmute1d
import CFT.LightconeBootstrap.LightconeBlock.Decomp
import CFT.LightconeBootstrap.LightconeBlock.EndpointBounds
import CFT.LightconeBootstrap.LightconeBlock.ReferencePairing
import CFT.LightconeBootstrap.LightconeBlock.RemainderBounds
import CFT.LightconeBootstrap.LightconeBlockBootstrap
import CFT.LightconeBootstrap.Primary.TransferKernel
import CFT.LightconeBootstrap.Primary.TriangularDecomp
import CFT.LightconeBootstrap.PrimaryBootstrap
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
     and series (`differentiableOn_integral_of_differentiableOn_of_norm_le`,
     `differentiableOn_tsum_of_differentiableOn_of_norm_le`).
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
   - **Three Top-Level Milestone Modules**:
     - `CFT.LightconeBootstrap.MonomialBootstrap`: Stage I quantitative $O((2k)^{-\gamma})$
       monomial lightcone bootstrap theorems against both the exact $t$-channel identity
       (`FourPointData.exists_const_abs_pairSpin_sub_identity_le`) and the universal Gamma limit
       (`FourPointData.exists_const_abs_pairSpin_sub_universal_le`).
     - `CFT.LightconeBootstrap.LightconeBlockBootstrap`: Stage II quantitative $O((2k)^{-\gamma})$
       1D lightcone-block bootstrap theorems (`FourPointData.exists_const_abs_lightcone_sub_exactIdentity_le`,
       `FourPointData.exists_const_abs_lightcone_sub_identity_le`,
       `FourPointData.exists_const_abs_lightcone_sub_universal_le`).
     - `CFT.LightconeBootstrap.PrimaryBootstrap`: Stage III quantitative $O((2k)^{-\gamma})$
       lightcone bootstrap for $d$-dimensional primary operators at all bounded twists $h \in [-N, N]$
       (`FourPointData.exists_const_abs_primary_allTwists_sub_gffPrimary_le`,
       `FourPointData.exists_const_abs_primary_unweighted_allTwists_le`).
   - **Stage I Supporting Modules (`CFT.LightconeBootstrap.Monomial.*`)**:
     - `CFT.LightconeBootstrap.Monomial.Decomp`: Monomial four-point data (`MonomialFourPointData`),
       folded spin-$2k$ Fourier projection (`laplaceSpinReal_eq_fourierProjSpin`), and canonical
       pushforward `FourPointData.toMonomialFourPointData`.
     - `CFT.LightconeBootstrap.Monomial.TwistGap`: Twist-gap condition (`MonomialFourPointData.HasTwistGap`)
       and $t$-channel identity dominance (`MonomialFourPointData.norm_eval_sub_crossIdentity_le`).
     - `CFT.LightconeBootstrap.Monomial.LaplaceBound`: Quantitative $O(K^{-1})$ Euler Gamma bounds
       (`exists_abs_rpow_mul_pochhammerCoeff_sub_inv_gamma_le`) and uniform real-axis Laplace bounds
       (`MonomialFourPointData.exists_uniform_laplaceSpinReal_sub_identity_bounds`).
     - `CFT.LightconeBootstrap.Monomial.ReferencePairing`: Lattice-shifted measures,
       `identityMonomialPairing`, `universalMonomialPairing`, and master Tauberian reduction
       (`MonomialFourPointData.exists_const_abs_rescaled_pairSpin_sub_le`).
   - **Stage II Supporting Modules (`CFT.LightconeBootstrap.LightconeBlock.*`)**:
     - `CFT.LightconeBootstrap.LightconeBlock.Transmute1d`: 1D fractional transmutation operators
       (`transmuteCore`, `transmuteOp`), `transmuteOp_block1d`, and `transmutePosWeight`.
     - `CFT.LightconeBootstrap.LightconeBlock.Decomp`: `LightconeBlockFourPointData`,
       `toTransmutedMonomialFourPointData`, `FourPointData.primaryTwistMeasure`, and
       `FourPointData.lightconeMeasure`.
     - `CFT.LightconeBootstrap.LightconeBlock.EndpointBounds`: Inner-derivative transmutation
       (`transmuteOpInner`), `transmuteOpInner_block1d`, and low-$x$ / high-$x$ split bounds
       (`norm_folded_integral_transmuteOpInner_le`).
     - `CFT.LightconeBootstrap.LightconeBlock.ReferencePairing`: Transmuted Laplace transforms and
       exact 3-term, 1-term, and universal pairings (`exactTransmutedIdentityPairing`,
       `transmutedIdentityPairing`, `transmutedUniversalPairing`), and `HasInnerTransmutedCrossing`.
     - `CFT.LightconeBootstrap.LightconeBlock.RemainderBounds`: 1D GFF collinear block transmutation
       (`hasSum_gffBlockCoeff_mul_transmuteOpInner_block1d`), untransmuted $t$-channel remainder
       derivative bounds (`exists_low_x_deriv_bounds_tChannelRemainder`,
       `exists_high_x_deriv_bounds_tChannelRemainder`), and $s$-channel collinear transmutation
       (`LightconeBlockFourPointData.transmuteOpInner_evalCollinear`).
   - **Stage III Supporting Modules (`CFT.LightconeBootstrap.Primary.*`)**:
     - `CFT.LightconeBootstrap.Primary.TransferKernel`: Rational weight shift ratio
       (`weightShiftRatio_eq_transmuteWeight_div`), smooth transfer functions
       (`collinearTransferFn`, `exists_c2_bound_collinearTransferFn`), and rescaled inverse
       transmutation weight bounds (`exists_c2_bound_cutoffInvTransmuteWeight`).
     - `CFT.LightconeBootstrap.Primary.TriangularDecomp`: Finite triangular collinear decomposition
       (`FourPointData.normLCPairing_eq_normPrimaryPairing_add_sum`) and recursive GFF
       $d$-dimensional primary coefficients and pairing (`gffPrimaryCoeff`, `gffPrimaryPairing`).
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
