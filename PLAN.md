# CFT Formalization Plan: Conformal Blocks and Four-Point Functions

## 1. Overview

The goal is to formalize four-point correlation functions expanded in conformal blocks in a way that:
1. Starts from **OPE data & Euclidean axioms** (`Corr.lean`, using `Blocks.lean` and `Gegenbauers.lean`), which are natural to justify from OS/Wightman or radial quantization axioms.
2. Analytically continues the conformal blocks and four-point correlator from the Euclidean $\rho$-disk ($\|\rho\| < 1$) to the **universal cover of the punctured polydisk** $\operatorname{UcPdisk} = \{(w_l, w_r) \in \mathbb{C}^2 \mid \operatorname{Re}(w_l) < 0, \operatorname{Re}(w_r) < 0\}$ where $(\rho_l, \rho_r) = (e^{w_l}, e^{w_r})$ (`Blocks_pdisk.lean` and `Corr_pdisk.lean`), and via `logRho` in `CutPlane.lean` to independent complex/lightcone coordinates $(z_l, z_r) \in \text{CutPlane} \times \text{CutPlane}$. Working in $(w_l, w_r)$ avoids all fractional-power branch cuts and provides the half-plane domain needed for Vitali's theorem.
3. Decomposes the polydisk conformal blocks at each left-moving twist level $e^{((\Delta - l)/2 + m) w_l}$ into finite positive sums of **1D (collinear) conformal blocks** $k_{\bar{h}}(e^{w_r})$ (`Blocks_1d.lean` and `Blocks_pdisk.lean`), providing the foundation for the **lightcone bootstrap**.

---

## 2. Module Dependency Graph

```text
CutPlane.lean          Gegenbauers.lean          Blocks_1d.lean     Analysis/DominatedHolomorphy.lean
      │                       │                        │                           │
      │                       ▼                        │                           │
      │                  Blocks.lean                   │                           │
      │                 ╱           ╲                  │                           │
      ▼                ▼             ▼                 ▼                           ▼
      ├────────► Corr.lean          Blocks_pdisk.lean ◄────────────────────────────┘
      │                ╲             ╱
      │                 ▼           ▼
      └──────────────► Corr_pdisk.lean
                              │
                              ▼
                     LightconeBootstrap/ ◄─── Analysis/{HermiteMeasure,TwoConstants,LaplaceTauberian}.lean
```

---

## 3. Status & Step-by-Step Implementation Plan

### Step 0: `CFT/CutPlane.lean` — **Done**
- [x] Defines the twice-cut plane `CutPlane = ℂ \ ((-∞, 0] ∪ [1, ∞))`.
- [x] Defines the radial coordinate map `rho : ℂ → ℂ` and proves `rho_norm_lt_one`, `rho_mem_slitPlane`, `conj_rho`, and `differentiableAt_rho` / `differentiableOn_rho`.
- [x] Defines the universal covers `UcDisk = {w : ℂ | w.re < 0}` and `UcPdisk = UcDisk ×ˢ UcDisk`, and the logarithmic radial map `logRho (z : ℂ) := Complex.log (rho z)` with `exp_logRho`, `logRho_mem_UcDisk`, `conj_logRho`, and `differentiableOn_logRho`.
- [x] Includes the identity theorem helpers (`eqOn_of_differentiableOn_of_eqOn_real_interval`, `eqOn_CutPlane_of_differentiableOn_of_eqOn_interval`) and neighborhood bounds (`exists_ball_pdisk_dom`, `add_I_mul_mem_CutPlane`, `sub_I_mul_mem_CutPlane`, `ofReal_mem_CutPlane`).

### Step 1: `CFT/Gegenbauers.lean` — **Done**
- [x] Defines the Gegenbauer (ultraspherical) polynomials $C_j^\nu(x)$ (`gegenbauer`) and the two-variable polynomial expansion (`geg_two_var_sum` / `geg_two_var_explicit`):
  $$(\rho_1 \rho_2)^j C_j^\nu\left(\frac{\rho_1/\rho_2 + \rho_2/\rho_1}{2}\right) = \sum_{a=0}^{j} c_{j, a}^\nu \rho_1^{2a} \rho_2^{2(j-a)}.$$
- [x] Proves non-negativity of the coefficients $c_{j, a}^\nu \ge 0$ for $\nu \ge 0$ (`geg_two_var_coeff_is_nonneg_real`, `geg_two_var_coeff_nonneg`) and the triangle inequality bound on the polydisk (`norm_geg_two_var_sum_le`).
- [x] Connects the Euclidean angular factor $\|\rho\|^j C_j^\nu(\cos(\arg \rho))$ to the two-variable sum on the Euclidean section $(\rho_l, \rho_r) = (\rho, \bar{\rho})$ (`geg_two_var_conj`).

### Step 2: `CFT/Blocks.lean` — **Structures Done; Properties & Casimir To Do**
- [x] Defines `descendantSpins l n : Finset ℕ` for the allowed spins $j$ at level $n$:
  $$j \in \{l + n, l + n - 2, \dots, \max(l - n, (l + n) \bmod 2)\}.$$
- [x] Defines `ConformalBlockLevel l n` (finite sum $\sum_{j \in \text{descendantSpins}(l, n)} A_{n, j} C_j^\nu(\cos\theta)$ with $A_{n, j} \ge 0$, absorbing the $1/C_j^\nu(1)$ normalization into $A_{n, j}$) and `ConformalBlock ν Δ l` (infinite sum over $n \in \mathbb{N}$ in $\rho \in \mathbb{C}$ with primary normalization $A_{0, l} = 1$, vanishing odd descendant levels `A_odd_level`, and radial summability at $\theta = 0$ for $r \in (0, 1)$).
- [ ] *(Later)*: Formalize the quadratic Casimir recursion relation for $A_{n, j}$ and deduce `summable_radial`.

### Step 3A: `CFT/Blocks_1d.lean` — **Done**
- [x] Defines the 1D (collinear / $SL(2, \mathbb{R})$) conformal block $k_h(e^w)$ of conformal weight $h$ in the coordinate $w \in \operatorname{UcDisk}$ (`block1dCoeff`, `block1d`):
  $$k_h(e^w) = e^{h w} \, {}_2F_1\!\left(h, \frac{1}{2}; h + \frac{1}{2}; e^{2w}\right) = \sum_{n=0}^{\infty} \frac{(h)_n (1/2)_n}{(h + 1/2)_n \, n!} e^{(h + 2n) w}.$$
- [x] Proves non-negativity (`block1dCoeff_nonneg`), positivity (`block1dCoeff_pos`), upper bound (`block1dCoeff_le_one`), and summability on the left half-plane $\operatorname{Re}(w) < 0$ (`summable_block1d`).
- [ ] *(Later)*: Add $z$-coordinate hypergeometric form $z^h \, {}_2F_1(h, h; 2h; z)$ and Euler integral representation when needed for the lightcone bootstrap.

### Step 3B: `CFT/Blocks_pdisk.lean` — **Polydisk Continuation & Holomorphy Done; Collinear Block Decomposition To Do**
- [x] Defines the direct polydisk continuation of `ConformalBlockLevel` and `ConformalBlock` (`evalTermPdisk`, `ConformalBlock.evalPdisk`) on $\operatorname{UcPdisk}$.
- [x] Defines `blockExp Δ l k = (Δ - l) / 2 + k`, `ConformalBlockLightconeLevel`, and `ConformalBlockLightcone Δ l`:
  - Expands the block as $\sum_{m=0}^{\infty} e^{((\Delta - l)/2 + m) w_l} g_m(w_r)$,
  - Leading twist ($m = 0$): $g_0(w_r)$ is proportional to a single 1D conformal block $k_{(\Delta + l)/2}(e^{w_r})$ from `Blocks_1d.lean` (`evalLevel_zero`),
  - Subleading twists ($m > 0$): $g_m(w_r)$ is a finite linear combination of 1D conformal blocks $k_{\bar{h}}(e^{w_r})$ with non-negative coefficients.
- [x] Proves `ConformalBlockLevel.evalTermPdisk_conj`, `ConformalBlock.evalPdisk_conj_eq_eval`, `ConformalBlock.evalPdisk_logRho_conj`, `ConformalBlockLevel.norm_evalTermPdisk_le_evalTerm_of_re_le`, `ConformalBlockLevel.norm_evalTermPdisk_le_evalTerm`, `ConformalBlock.norm_evalPdisk_le_eval_of_re_le`, `ConformalBlock.norm_evalPdisk_le_eval`, `ConformalBlockLevel.differentiable_evalTermPdisk`, and joint holomorphy on $\operatorname{UcPdisk}$ (`ConformalBlock.differentiableOn_evalPdisk` — **0 `sorry`s**).
- [ ] *(Later)*: Prove `ConformalBlock.exists_conformalBlockLightcone` equating `B.evalPdisk wl wr` with `L.eval wl wr` on $\operatorname{UcPdisk}$.

### Step 4: `CFT/Corr.lean` — **Done (0 `sorry`s)**
- [x] Defines `eval_correlator_eucl` and `FourPointData ν Δ_phi`:
  - Spectrum measure `mu_measure : Measure (ℝ × ℕ)` supported on unitary twist $\Delta - l \ge 0$ (`support_unitary`) and even spins $l$ (`support_even_spin`),
  - Family of `ConformalBlock ν Δ l`s with measurable expansion coefficients `measurable_A`,
  - Euclidean OPE convergence (`converges_correlator_eucl`) for $0 < \|\rho\| < 1$,
  - Euclidean crossing symmetry (`crossing_correlator_eucl`) on $z \in \text{CutPlane}$.

### Step 5: `CFT/Corr_pdisk.lean` — **Done (0 `sorry`s)**
- [x] Defines `eval_correlator_pdisk`, `FourPointData.correlator_pdisk`, `FourPointData.correlator` (via `logRho`), and `FourPointData.crossing_lhs` using the same OPE measure `corr.mu_measure` and continued blocks on $\operatorname{UcPdisk}$.
- [x] Proves polydisk OPE convergence (`FourPointData.converges_correlator_pdisk`) and joint holomorphy (`FourPointData.differentiableOn_correlator_pdisk`) on $\operatorname{UcPdisk}$ from `converges_correlator_eucl`, `support_unitary`, and `CFT.differentiableOn_integral_of_differentiableOn_of_norm_le`.
- [x] Proves Euclidean-section agreement (`FourPointData.correlator_pdisk_conj_eq_eucl` and `correlator_conj_eq_eucl`), separate holomorphy on `CutPlane` (`differentiableAt_correlator_comp`, `differentiableOn_correlator_left`, `differentiableOn_correlator_right`), and analytically continued two-variable crossing symmetry (`crossing_correlator` and `crossing_correlator_real`).

### Step 6: `CFT/Analysis/` & `CFT/LightconeBootstrap/` — **Done (0 `sorry`s; see [`CFT/LightconeBootstrap/PLAN.md`](CFT/LightconeBootstrap/PLAN.md))**
- [x] **Standalone Analysis Modules (`CFT/Analysis/`)**:
  - `DominatedHolomorphy.lean`: Cauchy Fréchet derivative and local Lipschitz bounds, joint measurability of derivatives, and joint holomorphy of locally dominated parametric integrals and series (`differentiableOn_integral_of_differentiableOn_of_norm_le`, `differentiableOn_tsum_of_differentiableOn_of_norm_le` — **100% `sorry`-free**).
  - `Vitali.lean`: 1D Cauchy derivative bounds, local uniform equicontinuity (`tendstoLocallyUniformlyOn_of_differentiableOn_of_norm_le`), and real-interval Vitali–Porter convergence theorems (`vitali_porter_real_interval`, `vitali_porter_ucDisk` — **100% `sorry`-free**).
  - `HermiteMeasure.lean`: Fejér kernel $K(u)$, Fejér–Hermite interpolant $H_\psi$, and non-asymptotic $C_c^2$ lattice measure estimate from bounded-frequency Fourier agreement on $[-2\pi, 2\pi]$ (**100% `sorry`-free**).
  - `TwoConstants.lean`: Explicit half-strip harmonic measure $\omega(\sigma, t)$ and Nevanlinna's Two-Constants Theorem on a vertical strip (`norm_le_two_constants_vertical_strip`, `norm_le_midpoint_two_constants` — **100% `sorry`-free**).
  - `LaplaceTauberian.lean`: Single-pair non-asymptotic and power-law Laplace-to-$C_c^2$ Tauberian theorems via exponential tilting (**100% `sorry`-free**).
- [x] **Quantitative Monomial Lightcone Bootstrap (`CFT/LightconeBootstrap/`)**:
  - `MonomialDecomp.lean`: Monomial decomposition `MonomialFourPointData`, canonical pushforward `FourPointData.toMonomialFourPointData` with evaluation identity `FourPointData.toMonomialFourPointData_eval`, folded spin-$J$ Fourier projection on $[-\pi/2, \pi/2]$ (`laplaceSpinReal_eq_fourierProjSpin`), and test-function pairing `pairSpin` (**100% `sorry`-free**).
  - `Gap.lean`: Twist gap (`HasLowerTwist`, `HasTwistGap`) and two-variable $t$-channel crossing in universal-cover coordinates (`norm_eval_sub_crossIdentity_le` — **100% `sorry`-free**).
  - `RealLaplaceBound.lean`: Uniform real-axis Laplace error bounds on compact negative intervals $[\sigma_-, \sigma_+] \subset (-\infty, 0)$ against both the exact finite-spin $t$-channel identity Laplace transform `identityLaplaceReal` ($\alpha = \min(2 h_{\text{gap}},\, 2\Delta_\phi - 1)$, `exists_uniform_laplaceSpinReal_sub_identity_bounds`) and the asymptotic universal double-twist Laplace transform `universalLaplaceReal` ($\alpha = \min(2 h_{\text{gap}},\, 1,\, 2\Delta_\phi - 1)$, `exists_uniform_laplaceSpinReal_bounds` — **100% `sorry`-free**).
  - `QuantitativeLargeSpin.lean`: Main quantitative large-spin theorems for $\varphi \in C_c^2(I)$ at even spin $J = 2k$ against the exact finite-spin $t$-channel identity pairing (`exists_const_abs_pairSpin_sub_identity_le`, `exists_const_abs_pairSpin_sub_identity_le_contDiff`, and `FourPointData.exists_const_abs_pairSpin_sub_identity_le`) and against the asymptotic $J \to \infty$ universal pairing (`exists_const_abs_pairSpin_sub_universal_le`, `exists_const_abs_pairSpin_sub_universal_le_contDiff`, and `FourPointData.exists_const_abs_pairSpin_sub_universal_le` — **100% `sorry`-free**).

