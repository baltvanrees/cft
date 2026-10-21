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
/-!
# Formalizing Conformal Field Theory in Lean 4

This library formalizes the analytic structure of four-point correlation functions of identical
scalar primary operators in reflection-positive conformal field theories in $d \ge 2$ dimensions
($\nu = (d-2)/2 \ge 0$), starting from Euclidean OPE convergence and crossing symmetry and
culminating in the **monomial lightcone bootstrap**.

## Module Overview

1. **Coordinate Domains & Identity Theorems (`CFT.CutPlane`)**:
   - The twice-cut cross-ratio plane $\operatorname{CutPlane} = \mathbb{C} \setminus
     ((-\infty, 0] \cup [1, \infty))$ and radial coordinate $\rho(z)$.
   - The left half-plane $\operatorname{UcDisk} = \{\operatorname{Re}(w) < 0\}$ (universal cover
     of the punctured unit $\rho$-disk via $\rho = e^w$), the polydisk cover
     $\operatorname{UcPdisk} = \operatorname{UcDisk} \times \operatorname{UcDisk}$, and the
     logarithmic radial map `logRho`.
2. **Gegenbauer Polynomials & Conformal Blocks (`CFT.Gegenbauers`, `CFT.Blocks`, `CFT.Blocks_1d`,
   `CFT.Blocks_pdisk`)**:
   - Gegenbauer polynomials $C_j^\nu$, two-variable binomial expansion `geg_two_var_sum`, and
     positivity of expansion coefficients for $\nu \ge 0$.
   - Euclidean conformal blocks (`ConformalBlock`) and their analytic continuation
     (`ConformalBlock.evalPdisk`) and joint holomorphy (`ConformalBlock.differentiableOn_evalPdisk`)
     on $\operatorname{UcPdisk}$.
   - One-dimensional ($SL(2, \mathbb{R})$) collinear conformal blocks (`block1d`).
3. **Four-Point Functions & Analytic Continuation of Crossing (`CFT.Corr`, `CFT.Corr_pdisk`)**:
   - Euclidean four-point data (`FourPointData`), polydisk OPE convergence
     (`FourPointData.converges_correlator_pdisk`), joint holomorphy
     (`FourPointData.differentiableOn_correlator_pdisk`), and analytic continuation of
     $s \leftrightarrow t$ crossing symmetry (`FourPointData.crossing_correlator`) from the
     Euclidean section $z_r = \bar{z}_l$ to independent complex variables
     $(z_l, z_r) \in \operatorname{CutPlane} \times \operatorname{CutPlane}$.
4. **Cauchy Derivative Bounds & Real-Interval Vitali Theorem (`CFT.Vitali`)**:
   - Cauchy derivative and local Lipschitz bounds for bounded holomorphic functions, holomorphy of
     locally dominated parametric integrals and series on $\mathbb{C} \times \mathbb{C}$, and the
     real-interval Vitali-type convergence theorem (`CFT.vitali_porter_real_interval`,
     `CFT.vitali_porter_ucDisk`).
-/
