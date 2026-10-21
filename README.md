# A roadmap for formalizing CFTs

This is a repository to formalize the structures appearing in reflection positive conformal field theories (CFTs) in $d > 2$ dimensions.

The plan (see [PLAN.md](PLAN.md)) is to first build all the necessary tools to analyze *four-point functions of identical scalar primary operators*. We will assume a conformal block decomposition and use it to prove results like Tauberian theorems for the asymptotics and light-cone bootstrap theorems. This approach will allow us to jump directly to mathematical physics questions of present-day interest.

In the longer run the idea is to introduce more fundamental axioms from which all these results will ultimately follow. This needs to be done carefully, and it will be beneficial to have concrete theorems to aim for.

Roughly speaking the idea will be to introduce as axioms conformal covariance and a Hilbert space in radial quantization. Postulating further the existence of a resolution of the identity will allow us to derive the state-operator correspondence, and thereby a convergent series expansion for $n$-point correlation functions of arbitrary local operators. 

Natural extensions will include the generalization to curved spaces and non-local operators like defects and interfaces.

We will always start the derivations in Euclidean signature. In the long run it might be possible to prove that the CFT axioms we postulate are fulfilled by a properly constructed QFT, for example the continuum limit of a lattice theory, and this will be most naturally done in Euclidean signature.

Our axioms will therefore mimic the OS axioms, although we have much more control in CFTs than in general QFTs. Lorentzian CFTs, and the associated Wightman functions, will be defined by analytic continuation.

While AI is used heavily throughout this repository, we aim for the documentation at https://baltvanrees.github.io/cft/docs/ to be maximally useful and educational. Currently all the files in the `CFT` folder have been human-verified, but those in sub-folders have not.

## Repository Structure and Current Milestones

A somewhat more detailed guide is maintained in [PLAN.md](PLAN.md) and in [CFT/MonomialBootstrap/PLAN.md](CFT/MonomialBootstrap/PLAN.md). See also the accompanying LaTeX note [doc/monomial_bootstrap.tex](doc/monomial_bootstrap.tex).

- **Complex Geometry & Coordinate Domains ([`CFT/CutPlane.lean`](CFT/CutPlane.lean))**:
  Defines the twice-cut cross-ratio plane $\operatorname{CutPlane} = \mathbb{C} \setminus ((-\infty, 0] \cup [1, \infty))$, the radial coordinate $\rho(z)$, the left half-plane $\operatorname{UcDisk} = \{\operatorname{Re}(w) < 0\}$ (universal cover of the punctured unit $\rho$-disk via $\rho = e^w$), the polydisk cover $\operatorname{UcPdisk} = \operatorname{UcDisk} \times \operatorname{UcDisk}$, and real-interval identity theorems.
- **Gegenbauer Polynomials & Conformal Blocks ([`CFT/Gegenbauers.lean`](CFT/Gegenbauers.lean), [`CFT/Blocks.lean`](CFT/Blocks.lean), [`CFT/Blocks_1d.lean`](CFT/Blocks_1d.lean), [`CFT/Blocks_pdisk.lean`](CFT/Blocks_pdisk.lean))**:
  Constructs the Gegenbauer polynomials $C_j^\nu$, proves the non-negativity of their two-variable binomial expansion coefficients for $\nu \ge 0$, defines Euclidean conformal blocks $G_{\Delta, l}(\rho)$, and analytically continues them to holomorphic functions on $\operatorname{UcPdisk}$.
- **Four-Point Functions & Analytic Continuation of Crossing Symmetry ([`CFT/Corr.lean`](CFT/Corr.lean), [`CFT/Corr_pdisk.lean`](CFT/Corr_pdisk.lean))**:
  Defines Euclidean four-point correlation functions (`FourPointData`), proves convergence and joint holomorphy of their analytic continuation on $\operatorname{UcPdisk}$, and analytically continues $s \leftrightarrow t$ crossing symmetry from the Euclidean section $z_r = \bar{z}_l$ to independent complex variables $(z_l, z_r) \in \operatorname{CutPlane} \times \operatorname{CutPlane}$.
- **Cauchy Fréchet Derivative Bounds & Vitali-Type Convergence ([`CFT/Vitali.lean`](CFT/Vitali.lean))**:
  Establishes Cauchy derivative and local Lipschitz bounds for bounded holomorphic functions, holomorphy of locally dominated parametric integrals and series on $\mathbb{C} \times \mathbb{C}$, and a real-interval Vitali-type convergence theorem on connected open domains (bypassing Montel's theorem via Tychonoff compactness in the pointwise product topology).
- **Monomial Lightcone Bootstrap ([`CFT/MonomialBootstrap/`](CFT/MonomialBootstrap/))**:
  Constructs the canonical monomial decomposition `FourPointData.toMonomialFourPointData` ([`MonomialDecomp.lean`](CFT/MonomialBootstrap/MonomialDecomp.lean)) and proves the universal large-spin asymptotics of the spin-$2k$ spectral measure $\mu_{2k}$ in any crossing-symmetric theory with a twist gap ([`FourierProj.lean`](CFT/MonomialBootstrap/FourierProj.lean), [`Gap.lean`](CFT/MonomialBootstrap/Gap.lean), [`IdentityProj.lean`](CFT/MonomialBootstrap/IdentityProj.lean), [`LargeSpin.lean`](CFT/MonomialBootstrap/LargeSpin.lean)):
  $$\lim_{k \to \infty} (2k)^{1 - 2\Delta_\phi} \int_{\mathbb{R}} \varphi(h) \, d\mu_{2k}(h) = \frac{2 \cdot 4^{2\Delta_\phi}}{\Gamma(2\Delta_\phi)} \sum_{n=0}^{\infty} \frac{(2\Delta_\phi)_n}{n!} \, \varphi(\Delta_\phi + n).$$
