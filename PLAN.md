# CFT Formalization Plan: Conformal Blocks and Four-Point Functions

## 1. Overview

The goal is to formalize four-point correlation functions expanded in conformal blocks in a way that:
1. Starts from **OPE data & Euclidean axioms** (`Corr.lean`, using `Blocks.lean` and `Gegenbauers.lean`), which are natural to justify from OS/Wightman or radial quantization axioms.
2. Analytically continues the conformal blocks and four-point correlator from the Euclidean $\rho$-disk ($\|\rho\| < 1$) to the **$(\rho_l, \rho_r)$ polydisk** (`Blocks_pdisk.lean` and `Corr_pdisk.lean`) and, via `CutPlane.lean`, to independent complex/lightcone coordinates $(z_l, z_r) \in \text{CutPlane} \times \text{CutPlane}$.
3. Decomposes the polydisk conformal blocks at each left-moving twist level $\rho_l^{(\Delta - l)/2 + m}$ into finite positive sums of **1D (collinear) conformal blocks** $k_{\bar{h}}(\rho_r)$ (`Blocks_1d.lean` and `Blocks_pdisk.lean`), providing the foundation for the **lightcone bootstrap**.

---

## 2. Module Dependency Graph

```text
CutPlane.lean          Gegenbauers.lean          Blocks_1d.lean
      │                       │                        │
      │                       ▼                        │
      │                  Blocks.lean                   │
      │                 ╱           ╲                  │
      ▼                ▼             ▼                 ▼
      ├────────► Corr.lean          Blocks_pdisk.lean ◄┘
      │                ╲             ╱
      │                 ▼           ▼
      └──────────────► Corr_pdisk.lean
```

---

## 3. Status & Step-by-Step Implementation Plan

### Step 0: `CFT/CutPlane.lean` — **Done**
- [x] Defines the twice-cut plane `CutPlane = ℂ \ ((-∞, 0] ∪ [1, ∞))`.
- [x] Defines the radial coordinate map `rho : ℂ → ℂ` and proves `rho_norm_lt_one`, `rho_mem_slitPlane`, `conj_rho`, and `differentiableAt_rho` / `differentiableOn_rho`.
- [x] Includes the identity theorem helpers (`eqOn_of_differentiableOn_of_eqOn_real_interval`, `eqOn_CutPlane_of_differentiableOn_of_eqOn_interval`) and neighborhood bounds (`exists_ball_pdisk_dom`, `add_I_mul_mem_CutPlane`, `sub_I_mul_mem_CutPlane`, `ofReal_mem_CutPlane`).

### Step 1: `CFT/Gegenbauers.lean` — **Done**
- [x] Defines the Gegenbauer (ultraspherical) polynomials $C_j^\nu(x)$ (`gegenbauer`) and the two-variable polynomial expansion (`geg_two_var_sum` / `geg_two_var_explicit`):
  $$(\rho_1 \rho_2)^j C_j^\nu\left(\frac{\rho_1/\rho_2 + \rho_2/\rho_1}{2}\right) = \sum_{a=0}^{j} c_{j, a}^\nu \rho_1^{2a} \rho_2^{2(j-a)}.$$
- [x] Proves non-negativity of the coefficients $c_{j, a}^\nu \ge 0$ for $\nu \ge 0$ (`geg_two_var_coeff_is_nonneg_real`, `geg_two_var_coeff_nonneg`) and the triangle inequality bound on the polydisk (`norm_geg_two_var_sum_le`).
- [x] Connects the Euclidean angular factor $\|\rho\|^j C_j^\nu(\cos(\arg \rho))$ to the two-variable sum on the Euclidean section $(\rho_l, \rho_r) = (\rho, \bar{\rho})$ (`geg_two_var_conj`).

### Step 2: `CFT/Blocks.lean` — **Structures Done; Properties & Casimir To Do**
- [x] Defines `descendantSpins l n : Finset ℕ` for the allowed spins $j$ at level $n$:
  $$j \in \{l + n, l + n - 2, \dots, \max(l - n, (l + n) \bmod 2)\}.$$
- [x] Defines `ConformalBlockLevel l n` (finite sum $\sum_{j \in \text{descendantSpins}(l, n)} A_{n, j} C_j^\nu(\cos\theta)$ with $A_{n, j} \ge 0$, absorbing the $1/C_j^\nu(1)$ normalization into $A_{n, j}$) and `ConformalBlock ν Δ l` (infinite sum over $n \in \mathbb{N}$ in $\rho \in \mathbb{C}$ with primary normalization $A_{0, l} = 1$ and radial summability at $\theta = 0$ for $r \in (0, 1)$).
- [ ] *(Later)*: Formalize the quadratic Casimir recursion relation for $A_{n, j}$ and deduce `summable_radial`.

### Step 3A: `CFT/Blocks_1d.lean` — **Done**
- [x] Defines the 1D (collinear / $SL(2, \mathbb{R})$) conformal block $k_h(\rho)$ of conformal weight $h$ in the $\rho$ coordinate (`block1dCoeff`, `block1d`):
  $$k_h(\rho) = \rho^h \, {}_2F_1\!\left(h, \frac{1}{2}; h + \frac{1}{2}; \rho^2\right) = \sum_{n=0}^{\infty} \frac{(h)_n (1/2)_n}{(h + 1/2)_n \, n!} \rho^{h + 2n}.$$
- [x] Proves non-negativity (`block1dCoeff_nonneg`), positivity (`block1dCoeff_pos`), upper bound (`block1dCoeff_le_one`), and summability on the punctured open unit disk $0 < \|\rho\| < 1$ (`summable_block1d`).
- [ ] *(Later)*: Add $z$-coordinate hypergeometric form $z^h \, {}_2F_1(h, h; 2h; z)$ and Euler integral representation when needed for the lightcone bootstrap.

### Step 3B: `CFT/Blocks_pdisk.lean` — **Structures Done; Bridge Theorems To Do**
- [x] Defines `blockExp Δ l k = (Δ - l) / 2 + k` and `ConformalBlockPdisk Δ l` (the double power series $\sum_{k_l, k_r} B_{k_l, k_r} \rho_l^{h_l(k_l)} \rho_r^{h_r(k_r)}$ with $B_{k_l, k_r} \ge 0$).
- [x] Defines the explicit bridge from `ConformalBlockLevel` and `ConformalBlock` (`pdiskCoeff`, `pdiskCoeff_nonneg`, `evalTermPdisk`, `ConformalBlock.evalPdisk`).
- [x] Defines `ConformalBlockLightconeLevel` and `ConformalBlockLightcone Δ l`:
  - Expands the block as $\sum_{m=0}^{\infty} \rho_l^{(\Delta - l)/2 + m} g_m(\rho_r)$,
  - Leading twist ($m = 0$): $g_0(\rho_r)$ is proportional to a single 1D conformal block $k_{(\Delta + l)/2}(\rho_r)$ from `Blocks_1d.lean` (`evalLevel_zero`),
  - Subleading twists ($m > 0$): $g_m(\rho_r)$ is a finite linear combination of 1D conformal blocks $k_{\bar{h}}(\rho_r)$ with non-negative coefficients.
- [x] States (with `sorry` for now) `ConformalBlock.exists_conformalBlockLightcone` decomposing any `ConformalBlock` into a `ConformalBlockLightcone`.
- [ ] Prove that `ConformalBlock.pdiskCoeff` satisfies `summable_real` from `summable_radial` (yielding `ConformalBlock.toConformalBlockPdisk`).
- [ ] Prove agreement of `evalPdisk` with `ConformalBlock.eval` on the Euclidean section $\rho_r = \bar{\rho}_l$ via `geg_two_var_conj`.
- [ ] Prove polydisk summability, radial bounds, and joint holomorphy (`HasFDerivAt` / `DifferentiableOn ℂ`) on $(\text{slitPlane} \cap B(0, 1))^2$.

### Step 4: `CFT/Corr.lean` — **Structures Done**
- [x] Defines `eval_correlator_eucl` and `FourPointData ν Δ_phi`:
  - Spectrum measure `mu_measure : Measure (ℝ × ℕ)` supported on unitary twist $\Delta - l \ge 0$,
  - Family of `ConformalBlock ν Δ l`s,
  - Euclidean OPE convergence (`converges_correlator_eucl`) for $0 < \|\rho\| < 1$,
  - Euclidean crossing symmetry (`crossing_correlator_eucl`) on $z \in \text{CutPlane}$.

### Step 5: `CFT/Corr_pdisk.lean` — **Structures Done; Analytic Continuation Theorems To Do**
- [x] Defines `eval_correlator_pdisk`, `FourPointData.correlator_pdisk`, `FourPointData.correlator_lightcone`, `FourPointData.correlator`, and `FourPointData.crossing_lhs` using the same OPE measure `corr.mu_measure` and polydisk-continued blocks.
- [ ] Prove polydisk OPE convergence and dominated differentiation (joint holomorphy in $(\rho_l, \rho_r)$) from `FourPointData.converges_correlator_eucl`.
- [ ] Prove agreement with the Euclidean four-point function on $z_r = \bar{z}_l$.
- [ ] Analytically continue crossing symmetry to independent $(z_l, z_r) \in \text{CutPlane} \times \text{CutPlane}$ (and in particular real lightcone coordinates $x_l, x_r \in (0, 1)$).
