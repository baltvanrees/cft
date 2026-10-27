# Quantitative Conformal-Block Lightcone Bootstrap (Plan)

## 1. Goal & Mathematical Overview

This document outlines the plan to upgrade the quantitative monomial lightcone bootstrap in `CFT/LightconeBootstrap/` (`QuantitativeLargeSpin.lean`) to a **quantitative lightcone bootstrap for $d$-dimensional primary operators** across all double-twist families $h \approx \Delta_\phi + M$ ($M \in \mathbb{N}$) at large even spin $l = 2k$, with the **sharp power-law error rate** $O((2k)^{-\gamma})$ for all $\Delta_\phi > 0$, $h_{\text{gap}} > 0$, and
$$0 < \gamma < \min(2 h_{\text{gap}},\, 2\Delta_\phi).$$

### Core Strategy: Fractional Transmutation ($\mathcal{L}_0$) + Axiomatized Lightcone Block Decomposition

Instead of inverting the 1D conformal blocks after the Tauberian theorem (which loses $(2k)^{1/2}$ in the error bound and introduces an $h$-dependent matrix inversion), we combine two ingredients **before** the Tauberian theorem:

1. **Axiomatized Lightcone Block Decomposition (Option A — `ConformalBlockLightcone` in `CFT/Blocks_pdisk.lean`)**:
   Following the same design philosophy as `CFT/Blocks.lean` (which axiomatizes the Euclidean descendant-level coefficients $A_{n, j}$ rather than deriving them from the quadratic Casimir PDE), we keep the Casimir derivation of `exists_conformalBlockLightcone` on hold and instead equip `FourPointData` directly with a family of `ConformalBlockLightcone` decompositions (`CFT/Blocks_pdisk.lean`):
   $$G_{\Delta, l}^{\text{pdisk}}(w_l, w_r) = \sum_{m=0}^{\infty} e^{\operatorname{blockExp}(\Delta, l, m) \, w_l} \sum_{k_r \in \text{support}_m} C_{m, k_r}(\Delta, l) \, \operatorname{block1d}\bigl(\operatorname{blockExp}(\Delta, l, k_r),\, w_r\bigr),$$
   where $\operatorname{blockExp}(\Delta, l, k) = \frac{\Delta - l}{2} + k = h + k$, the leading twist level $m = 0$ consists of a **single** 1D block at $k_r = l$ ($\bar{h} = h + l$) with positive coefficient $C_{0, l}(\Delta, l) > 0$ (`support_zero`, `C_zero_pos`), and each subleading twist level $m \ge 1$ is a **finite** non-negative linear combination of 1D blocks (`C_nonneg`, `C_support`).

2. **1D Fractional Transmutation Operator ($\mathcal{L}_0$) on $\operatorname{UcDisk}$**:
   We define a linear differential-integral operator $\mathcal{L}_0$ acting **purely on the right coordinate $w_r \in \operatorname{UcDisk}$** (completely independent of $h$ and $J$) that transmutes every 1D collinear block `block1d h̄ wr` into a single exponential monomial:
   $$\mathcal{L}_0\bigl[\operatorname{block1d}(\bar{h}, \cdot)\bigr](w_r) = w_0(\bar{h}) \, e^{\bar{h} w_r}, \qquad w_0(\bar{h}) := \left(\bar{h} - \frac{1}{2}\right) \frac{\Gamma(\bar{h} + 1/2)}{\Gamma(\bar{h})} \sim \bar{h}^{3/2}.$$
   - **Why no $4^{\bar{h}}$ factor appears**: In `CFT/Blocks_1d.lean`, `block1d h̄ wr` is already normalized so that its leading coefficient at $e^{\bar{h} w_r}$ is $1$ (`block1dCoeff h̄ 0 = 1`), i.e., $\bigl(\operatorname{zOfW}(w_r)\bigr)^{\bar{h}} {}_2F_1(\bar{h}, \bar{h}; 2\bar{h}; \operatorname{zOfW}(w_r)) = 4^{\bar{h}} \operatorname{block1d}(\bar{h}, w_r)$. By linearity of $\mathcal{L}_0$, the $4^{\bar{h}}$ factors cancel on both sides.
   - **Positivity preservation**: For every spin $J = 2k \ge 2$ and unitary left twist $h \ge 0$, $\bar{h} = h + 2k \ge 2 > 1/2$, so $w_0(h + 2k) > 0$. Thus, applying $\mathcal{L}_0$ to the correlator $\mathcal{G}_{\text{pdisk}}(w_l, w_r)$ produces a **valid `MonomialFourPointData`** with non-negative measures
     $$d\mu^{\text{trans}}_J(h) = w_0(h + J) \, d\mu^{\text{LC}}_J(h).$$
   - **Why $\mathcal{L}_0$ completely solves the $\Delta_\phi \le 1/2$ problem**:
     In the monomial bootstrap (`RealLaplaceBound.lean`), the $t$-channel identity had singularity $(1 - e^{w_r})^{-2\Delta_\phi}$, so its spin-$2k$ integral grew like $(2k)^{2\Delta_\phi - 1}$ while the outer contour $|\theta| \sim \pi/2$ was $O(1)$; dividing $O(1)$ by $(2k)^{2\Delta_\phi - 1}$ gave an error $(2k)^{1 - 2\Delta_\phi}$, which required $\Delta_\phi > 1/2$.
     Under $\mathcal{L}_0$, the operator has net order $+1/2$ in $(1 - \operatorname{zOfW}(w_r)) = \bigl(\frac{1 - e^{w_r}}{1 + e^{w_r}}\bigr)^2$, which is **net order $+1$ in $(1 - e^{w_r})$**! Thus $\mathcal{L}_0$ boosts the $t$-channel identity singularity from $(1 - e^{w_r})^{-2\Delta_\phi}$ to
     $$(1 - e^{w_r})^{-2\Delta_\phi - 1},$$
     whose spin-$2k$ Fourier projection grows like **$(2k)^{2\Delta_\phi}$** (matching $w_0(h + 2k) \times (2k)^{2\Delta_\phi - 3/2} \sim (2k)^{3/2} \cdot (2k)^{2\Delta_\phi - 3/2} = (2k)^{2\Delta_\phi}$)!
     Dividing the $O(1)$ outer-contour contribution by $(2k)^{2\Delta_\phi}$ gives $(2k)^{-2\Delta_\phi}$, which decays for **all $\Delta_\phi > 0$**!
   - **Sharp Tauberian bound with zero loss**: Applying our existing Tauberian pipeline (`HermiteMeasure.lean`, `TwoConstants.lean`, `LaplaceTauberian.lean`) directly to the normalized transmuted positive measure $\tilde{\mu}^{\text{trans}}_{2k} := (2k)^{-2\Delta_\phi} \mu^{\text{trans}}_{2k}$ gives a relative error $O((2k)^{-\gamma})$ for **all** $0 < \gamma < \min(2 h_{\text{gap}},\, 2\Delta_\phi)$ and **all** $\Delta_\phi > 0$. Dividing test functions $\varphi \in C_c^2(I_M)$ by $(2k)^{-3/2} w_0(h + 2k) \sim 1$ then yields the exact $(2k)^{2\Delta_\phi - 3/2}$ primary asymptotics with no loss in the exponent $\gamma$.

---

## 2. Dictionary of Notation (Matching Current Lean Files)

| Mathematical Object | Lean Name / File | Definition / Formula |
|---|---|---|
| Universal cover of punctured disk | `UcDisk`, `UcPdisk` (`CutPlane.lean`) | $\{w \in \mathbb{C} \mid \operatorname{Re}(w) < 0\}$, $\rho = e^w$ |
| Forward radial map $z \mapsto \rho(z)$ | `rho`, `logRho` (`CutPlane.lean`) | $\rho(z) = \frac{z}{(1 + \sqrt{1 - z})^2}$, $\operatorname{logRho}(z) = \log \rho(z)$ |
| Inverse radial map $w \mapsto z(w)$ | `zOfW` (`Gap.lean`) | $\operatorname{zOfW}(w) = \frac{4 e^w}{(1 + e^w)^2} \in \operatorname{CutPlane}$ |
| Crossed coordinate $w \mapsto w^{\text{cross}}$ | `crossW` (`Gap.lean`) | $\operatorname{crossW}(w) = \operatorname{logRho}(1 - \operatorname{zOfW}(w))$ |
| $t$-channel crossing factor | `crossFactor`, `crossIdentity` (`Gap.lean`) | $\operatorname{crossFactor}(\Delta_\phi, w) = 4^{\Delta_\phi} e^{\Delta_\phi w} (1 - e^w)^{-2\Delta_\phi}$ |
| 1D collinear block $k_{\bar{h}}(e^{w_r})$ | `block1d`, `block1dCoeff` (`Blocks_1d.lean`) | $\sum_{n=0}^\infty \frac{(\bar{h})_n (1/2)_n}{(\bar{h} + 1/2)_n \, n!} e^{(\bar{h} + 2n) w_r}$ |
| Scaling exponent $h + k$ | `blockExp` (`Blocks_pdisk.lean`) | $\operatorname{blockExp}(\Delta, l, k) = \frac{\Delta - l}{2} + k$ |
| Lightcone block decomposition | `ConformalBlockLightcone` (`Blocks_pdisk.lean`) | $\sum_{m=0}^\infty e^{\operatorname{blockExp}(\Delta, l, m) w_l} g_m(w_r)$ |
| Polydisk block & correlator | `evalPdisk`, `correlator_pdisk` (`Corr_pdisk.lean`) | $\mathcal{G}_{\text{pdisk}}(w_l, w_r) = \int G_{\Delta, l}^{\text{pdisk}}(w_l, w_r) \, d\mu(\Delta, l)$ |
| Monomial spectral data | `MonomialFourPointData` (`MonomialDecomp.lean`) | $\sum_{J \in \mathbb{Z}} \int_{\mathbb{R}} e^{h w_l + (h + J) w_r} \, d\mu_J(h)$ |
| Rescaled $z$-coordinate in $\operatorname{UcDisk}$ | `scaleW` (`Transmute1d.lean`) | $\operatorname{scaleW}(t, w) := \operatorname{logRho}(t \cdot \operatorname{zOfW}(w))$ for $t \in (0, 1)$ |
| Half-binomial coefficient $b_k$ | `halfBinom` (`Transmute1d.lean`) | $b_k = \frac{(1/2)_k}{k!}$ |
| Core transmutation kernel & operator | `transmuteKernel`, `transmuteCore` (`Transmute1d.lean`) | $(\operatorname{transmuteCore} f)(w) := \frac{1}{\sqrt{\pi}} \int_0^1 s^{-1/2}(1 - s)^{-3/2}(1 - s e^{2w}) f(w + \log s) \, ds$ |
| $H$-independent transmutation operator | `transmuteOp` ($\mathcal{L}_0$) (`Transmute1d.lean`) | $(\mathcal{L}_0 f)(w) := \bigl(\partial_w - \frac{1}{2}\bigr)^2 (\operatorname{transmuteCore} f)(w)$ |
| Transmutation multipliers | `transmuteCoreWeight`, `transmuteWeight` ($w_0$) (`Transmute1d.lean`) | $\operatorname{transmuteCoreWeight}(\bar{h}) = \frac{\Gamma(\bar{h} - 1/2)}{\Gamma(\bar{h})}$, $w_0(\bar{h}) = (\bar{h} - \frac{1}{2}) \frac{\Gamma(\bar{h} + 1/2)}{\Gamma(\bar{h})}$ |
| Lightcone-block four-point data | `LightconeBlockFourPointData` (`LightconeBlockDecomp.lean`) | Packages $\mu^{\text{LC}}_J$, $\mu^{\text{prim}}_l$, $C_{0, l} > 0$, $h_{\text{gap}}$, and `toTransmutedMonomialFourPointData` |
| Transmuted universal & identity Laplace | `transmutedUniversalLaplaceReal`, `transmutedIdentityLaplaceReal` (`TransmutedRealLaplace.lean`) | $\frac{2 \cdot 4^{2\Delta_\phi}}{\Gamma(\Delta_\phi)^2} e^{\Delta_\phi \sigma} (1 - e^\sigma)^{-2\Delta_\phi}$ and its exact finite-spin mixed binomial series |
| Leading-twist primary bootstrap theorems | `exists_const_abs_primary_leadingTwist_sub_identity_le`, `exists_const_abs_primary_leadingTwist_sub_universal_le` (`PrimaryLargeSpin.lean`) | Quantitative $O((2k)^{-\gamma})$ primary operator bootstrap for all $\Delta_\phi > 0, h_{\text{gap}} > 0$ |

---

## 3. Detailed Mathematical Pipeline

### Stage 1: The 1D Transmutation Operator $\mathcal{L}_0$ on $\operatorname{UcDisk}$ (`Transmute1d.lean`)

1. **Star-convexity of $\operatorname{CutPlane}$ from $0$ and the map `scaleW`**:
   - For any $z \in \operatorname{CutPlane}$ and $t \in (0, 1)$, $t z \in \operatorname{CutPlane}$: if $\operatorname{Im}(z) \ne 0$ then $\operatorname{Im}(t z) = t \operatorname{Im}(z) \ne 0$, while if $z \in (0, 1)$ then $t z \in (0, 1)$.
   - Consequently, for $w \in \operatorname{UcDisk}$ with $\operatorname{Im}(w) \in (-\pi, \pi)$ and $t \in (0, 1)$, we define
     $$\operatorname{scaleW}(t, w) := \operatorname{logRho}\bigl(t \cdot \operatorname{zOfW}(w)\bigr) \in \operatorname{UcDisk}.$$
   - Key properties of `scaleW`:
     - $\operatorname{zOfW}(\operatorname{scaleW}(t, w)) = t \cdot \operatorname{zOfW}(w)$.
     - $e^{\operatorname{Re}(\operatorname{scaleW}(t, w))} = \|\rho(t \cdot \operatorname{zOfW}(w))\| \le t \|\operatorname{zOfW}(w)\|$, so as $t \downarrow 0$, $\operatorname{Re}(\operatorname{scaleW}(t, w)) \to -\infty$ and any function $f(w) = O(e^{\bar{h} \operatorname{Re}(w)})$ decays like $t^{\bar{h}}$.
     - Because $D_w := \frac{1 + e^w}{1 - e^w} \partial_w$ is the pullback of $z \partial_z$ along $z = \operatorname{zOfW}(w)$, $D_w$ commutes with $K_{1/2}$:
       $$K_{1/2}\bigl(D_w(D_w - \tfrac{1}{2}) f\bigr)(w) - \operatorname{zOfW}(w) K_{1/2}(D_w^2 f)(w) = \bigl[(1 - \operatorname{zOfW}(w)) D_w^2 - \tfrac{1}{2} D_w\bigr] (K_{1/2} f)(w).$$

2. **Action of $\mathcal{L}_0$ on `block1d`**:
   - By analytic continuation on the strip $\{w \in \operatorname{UcDisk} \mid \operatorname{Im}(w) \in (-\pi, \pi)\}$ (`eqOn_of_differentiableOn_of_eqOn_real_interval` in `CutPlane.lean`), it suffices to prove the transmutation identity on the negative real axis $w = \sigma < 0$.
   - Using Euler's Beta integral (`Complex.betaIntegral` in Mathlib) and Goursat's quadratic hypergeometric identity
     $${}_2F_1\!\left(\bar{h}, \bar{h} - \frac{1}{2}; 2\bar{h}; \frac{4 e^w}{(1 + e^w)^2}\right) = (1 + e^w)^{2\bar{h} - 1},$$
     applying $\mathcal{L}_0$ to $\operatorname{block1d}(\bar{h}, w)$ collapses the entire descendant series to a **single exponential**:
     $$\mathcal{L}_0\bigl[\operatorname{block1d}(\bar{h}, \cdot)\bigr](w_r) = w_0(\bar{h}) \, e^{\bar{h} w_r}, \qquad w_0(\bar{h}) = \left(\bar{h} - \frac{1}{2}\right) \frac{\Gamma(\bar{h} + 1/2)}{\Gamma(\bar{h})}.$$
   - For $\bar{h} = 0$ (the identity block $\operatorname{block1d}(0, w_r) = 1$), $D_w(1) = 0$ so $\mathcal{L}_0(1) = 0 = w_0(0)$.

---

### Stage 2: Axiomatized Lightcone Block Decomposition (`LightconeBlockDecomp.lean`)

Following **Option A** (keeping the quadratic Casimir derivation of `exists_conformalBlockLightcone` on hold, just as `CFT/Blocks.lean` keeps the Casimir recursion for $A_{n, j}$ on hold):

1. **Equipping `FourPointData` with `ConformalBlockLightcone`**:
   - We define a structure `LightconeBlockFourPointData` (or a predicate on `FourPointData ν Δ_phi`) providing for each $(\Delta, l)$ a `ConformalBlockLightcone Δ l` (`CFT/Blocks_pdisk.lean`) such that:
     - `B.evalPdisk wl wr = L.eval wl wr` for all $(w_l, w_r) \in \operatorname{UcPdisk}$,
     - the lightcone block coefficients $C_{m, k_r}(\Delta, l)$ are measurable across $(\Delta, l)$,
     - at leading twist $m = 0$, $\text{support}_0 = \{l\}$ and $C_{0, l}(\Delta, l) = \frac{(\nu)_l}{l!}$,
     - at subleading twist $m \ge 1$, $\text{support}_m \subseteq \{k_r \in \mathbb{N} \mid k_r \equiv l + m \pmod 2,\; |k_r - (l + m)| \le 2m\}$ (at most $2m + 1$ terms).

2. **Result of Applying $\mathcal{L}_0$ to a `ConformalBlockLightcone`**:
   - Because each level $g_m(w_r) = \sum_{k_r \in \text{support}_m} C_{m, k_r}(\Delta, l) \, \operatorname{block1d}(\operatorname{blockExp}(\Delta, l, k_r), w_r)$ is a **finite** sum of 1D blocks, linearity of $\mathcal{L}_0$ immediately gives:
     $$\mathcal{L}_0\bigl[g_m\bigr](w_r) = \sum_{k_r \in \text{support}_m} C_{m, k_r}(\Delta, l) \, w_0\bigl(\operatorname{blockExp}(\Delta, l, k_r)\bigr) \, e^{\operatorname{blockExp}(\Delta, l, k_r) w_r}.$$
   - In particular, at **leading twist $m = 0$**, a primary of spin $l = 2k$ and left twist $h = \frac{\Delta - 2k}{2}$ contributes **only a single monomial at spin $J = 2k$**:
     $$\frac{(\nu)_{2k}}{(2k)!} \, w_0(h + 2k) \, e^{h w_l + (h + 2k) w_r}.$$

---

### Stage 3: Transmuted `MonomialFourPointData` & $t$-Channel Real Laplace Bound (`TransmutedRealLaplace.lean`)

1. **The Transmuted Correlator as a `MonomialFourPointData`**:
   - Applying $\mathcal{L}_0$ in the right variable $w_r$ to `corr.correlator_pdisk wl wr` defines the transmuted correlator
     $$\mathcal{G}_{\text{trans}}(w_l, w_r) := \mathcal{L}_0\bigl[\text{corr.correlator\_pdisk } w_l\bigr](w_r).$$
   - Moving $\mathcal{L}_0$ inside the OPE integral and lightcone sum (justified by dominated differentiation and Fubini on $\operatorname{UcPdisk}$ since $\operatorname{Re}(\operatorname{scaleW}(t, w_r)) \le \operatorname{Re}(w_r) < 0$), $\mathcal{G}_{\text{trans}}$ is the evaluation of a `MonomialFourPointData` (`corr.toTransmutedMonomialFourPointData`) whose spin-$2k$ spectral measure is:
     $$\mu^{\text{trans}}_{2k} = \frac{(\nu)_{2k}}{(2k)!} w_0(h + 2k) \, \mu^{\text{prim}}_{2k} + \sum_{m=1}^{\infty} \sum_{s = -m}^{m} \bigl(\text{pushforward of } \mu^{\text{prim}}_{2(k - s)} \text{ by } h \mapsto h + m\bigr).$$
   - Crucially, for all $k \ge 1$, $\mu^{\text{trans}}_{2k}$ is a **positive measure**, and the folded spin-$2k$ Fourier projection from `MonomialDecomp.lean` (`laplaceSpinReal_eq_fourierProjSpin`) applies to $\mathcal{G}_{\text{trans}}$ **verbatim**!

2. **Action of $\mathcal{L}_0$ on `crossIdentity` and $t$-Channel Remainder**:
   - By two-variable crossing symmetry (`eval_eq_cross` in `Gap.lean`),
     $$\text{corr.correlator\_pdisk } w_l\, w_r = \operatorname{crossIdentity}(\Delta_\phi, w_l, w_r) + R(w_l, w_r),$$
     where $\operatorname{crossIdentity}(\Delta_\phi, w_l, w_r) = \operatorname{crossFactor}(\Delta_\phi, w_l) \cdot \operatorname{crossFactor}(\Delta_\phi, w_r)$.
   - Since $\mathcal{L}_0$ acts only on $w_r$,
     $$\mathcal{L}_0\bigl[\operatorname{crossIdentity}(\Delta_\phi, w_l, \cdot)\bigr](w_r) = \operatorname{crossFactor}(\Delta_\phi, w_l) \cdot \mathcal{L}_0\bigl[\operatorname{crossFactor}(\Delta_\phi, \cdot)\bigr](w_r).$$
   - **Exact $t$-channel identity transmutation**:
     In the $z$-coordinate, $\operatorname{crossFactor}(\Delta_\phi, w_r) = z_r^{\Delta_\phi} (1 - z_r)^{-\Delta_\phi}$. Applying $K_{1/2}$ produces a ${}_2F_1$ function whose quadratic transformation back to $e^{w_r}$ has leading singularity $(1 - e^{w_r})^{-2\Delta_\phi - 1}$ as $w_r \to 0$, with spin-$2k$ Fourier coefficient growing like **$(2k)^{2\Delta_\phi}$** for all $\Delta_\phi > 0$.
   - **$t$-Channel Remainder Bound under $\mathcal{L}_0$ (Valid for All $\Delta_\phi > 0$)**:
     Using Cauchy's derivative bound (`norm_deriv_le_of_forall_mem_sphere_norm_le` from `CFT/Analysis/DominatedHolomorphy.lean`) on a disk of radius $\propto |1 - e^{w_r}|$ around $w_r$ together with `norm_eval_sub_crossIdentity_le` from `Gap.lean`:
     $$\bigl\|\mathcal{L}_0[R(w_l, \cdot)](w_r)\bigr\| \le C \, \|1 - e^{w_r}\|^{2 h_{\text{gap}} - 2\Delta_\phi - 1}.$$
     Integrating over the folded contour $w_r = -1/(2k) + i\theta$ ($\theta \in [-\pi/2, \pi/2]$) bounds the remainder integral by $O\bigl((2k)^{2\Delta_\phi - 2 h_{\text{gap}}}\bigr) + O(1)$. Dividing by the $(2k)^{2\Delta_\phi}$ normalization factor gives the uniform real-axis Laplace error bound:
     $$\sup_{\sigma \in [\sigma_-, \sigma_+]} (2k)^{-2\Delta_\phi} \Bigl|L^{\text{trans}}_{2k}(\sigma) - L^{\text{trans, id}}_{2k}(\Delta_\phi, \sigma)\Bigr| \le C_{[\sigma_-, \sigma_+]} \, (2k)^{-\min(2 h_{\text{gap}},\, 2\Delta_\phi)},$$
     which holds for **all $\Delta_\phi > 0$ and $h_{\text{gap}} > 0$** (completely eliminating the $\Delta_\phi > 1/2$ barrier)!

---

### Stage 4: Tauberian Theorem & Extraction of Primary Measures (`PrimaryLargeSpin.lean`)

1. **Quantitative Tauberian Bound for the Transmuted Measure $\mu^{\text{trans}}_{2k}$**:
   - Normalizing $\tilde{\mu}^{\text{trans}}_{2k} := (2k)^{-2\Delta_\phi} \mu^{\text{trans}}_{2k}$, applying `LaplaceTauberian.lean` (`exists_const_abs_integral_sub_le_rpow`) directly to the positive measures $\tilde{\mu}^{\text{trans}}_{2k}$ yields, for every compact interval $I \subset \mathbb{R}$, every $\Delta_\phi > 0$, $h_{\text{gap}} > 0$, $0 < \gamma < \min(2 h_{\text{gap}},\, 2\Delta_\phi)$, and every $\psi \in C_c^2(I)$:
     $$\left|\int_{\mathbb{R}} \psi(h) \, d\bigl(\tilde{\mu}^{\text{trans}}_{2k} - \tilde{\mu}^{\text{trans, id}}_{2k}\bigr)(h)\right| \le C_{I, \gamma} \, (2k)^{-\gamma} \, \|\psi\|_{C^2}.$$

2. **Leading-Twist Primary Operators ($M = 0$, $h \approx \Delta_\phi$)**:
   - For any compact interval $I_0 \subset (-\infty, \Delta_\phi + 1)$ and $\varphi \in C_c^2(I_0)$, all $m \ge 1$ subleading lightcone levels vanish on $I_0$ when the non-identity spectrum has twist gap $\Delta_\phi - \delta$, so $\mu^{\text{trans}}_{2k}$ on $I_0$ equals $\frac{(\nu)_{2k}}{(2k)!} w_0(h + 2k) \, \mu^{\text{prim}}_{2k}$.
   - Setting $\psi_k(h) := \frac{(2k)^{3/2}}{w_0(h + 2k)} \varphi(h) \in C_c^2(I_0)$ (which satisfies $\|\psi_k\|_{C^2} \le C_{I_0} \|\varphi\|_{C^2}$ uniformly in $k \ge 1$) immediately yields the **leading-twist $d$-dimensional primary bootstrap theorem**:
     $$\boxed{\left|(2k)^{3/2 - 2\Delta_\phi} \frac{(\nu)_{2k}}{(2k)!} \int_{\mathbb{R}} \varphi(h) \, d\mu^{\text{prim}}_{2k}(h) - C^{\text{GFF, LC}}_0(\Delta_\phi) \, \varphi(\Delta_\phi)\right| \le C_{I_0, \gamma} \, (2k)^{-\gamma} \, \|\varphi\|_{C^2}}$$
     for all $0 < \gamma < \min(2 h_{\text{gap}},\, 2\Delta_\phi)$ (or dividing by $\frac{(\nu)_{2k}}{(2k)!} \sim \frac{(2k)^{\nu - 1}}{\Gamma(\nu)}$ to state directly for $(2k)^{5/2 - \nu - 2\Delta_\phi} \mu^{\text{prim}}_{2k}$).

3. **Subleading Double-Twist Families ($M \ge 1$, $h \approx \Delta_\phi + M$)**:
   - By strong induction on $M \in \mathbb{N}$, on $I_M \subset (\Delta_\phi + M - 1, \Delta_\phi + M + 1)$ we subtract the finite sum of at most $2m + 1$ known lower-twist primary measures $\mu^{\text{prim}}_{2(k - s)}$ ($1 \le m \le M, -m \le s \le m$), preserving the full error bound $O((2k)^{-\gamma})$.

---

## 4. File Structure

The analysis engine in `CFT/Analysis/` and the core monomial projection in `CFT/LightconeBootstrap/MonomialDecomp.lean`, `Gap.lean`, and `RealLaplaceBound.lean` are **reused intact**, and four modular files implement the $d$-dimensional primary bootstrap in `CFT/LightconeBootstrap/`:

```text
CFT/Blocks_pdisk.lean               (ConformalBlockLightcone & ConformalBlockLightconeLevel — 0 sorry's)
       │
       ▼
CFT/LightconeBootstrap/
  ├── PLAN.md                       (Completed monomial lightcone bootstrap plan)
  ├── PLAN_CONFORMAL_BLOCKS.md      (This file: completed d-dimensional primary bootstrap plan)
  ├── MonomialDecomp.lean           (MonomialFourPointData & folded spin-J projection — 0 sorry's)
  ├── Gap.lean                      (zOfW, crossW, crossFactor, & t-channel gap bounds — 0 sorry's)
  ├── RealLaplaceBound.lean         (Mixed-binomial series & monomial real-axis Laplace bounds — 0 sorry's)
  ├── QuantitativeLargeSpin.lean    (Monomial C_c^2 bootstrap theorems — 0 sorry's)
  │
  ├── Transmute1d.lean              (Stage 1: halfBinom, transmuteCore, transmute1d, transmuteOp L_0,
  │                                  transmutePosWeight, & L_0[block1d H] = w_0(H) e^{H w_r} — 0 sorry's)
  ├── LightconeBlockDecomp.lean     (Stage 2: Action of L_0 on ConformalBlockLightcone, Option A
  │                                  LightconeBlockFourPointData, & toTransmutedMonomialFourPointData — 0 sorry's)
  ├── TransmutedRealLaplace.lean    (Stage 3: transmutedIdentityLaplaceReal, transmutedUniversalLaplaceReal,
  │                                  & uniform real-axis Laplace bounds for all Δ_φ > 0 — 0 sorry's)
  └── PrimaryLargeSpin.lean         (Stage 4: Tauberian bounds for transmuted measure & leading-twist
                                     d-dimensional primary bootstrap theorems for all Δ_φ > 0 — 0 sorry's)
```

---

## 5. Step-by-Step Implementation Checklist

### Phase 1: 1D Fractional Transmutation on `UcDisk` (`Transmute1d.lean`) — **Done (0 `sorry`s)**
- [x] **Step 1.1 (Half-Binomial Coefficients & Partial-Fraction Identity)**:
  - Defined `halfBinom k = (1/2)_k / k!` and proved the convolution identity `sum_halfBinom_mul_halfBinom` ($\sum_{k=0}^m b_k b_{m - k} = 1$) and the partial-fraction identity `sum_halfBinom_div_add_eq_pochhammer_div` ($\sum_{k=0}^m \frac{b_k b_{m - k}}{X + k} = \frac{(X + 1/2)_m}{(X)_{m + 1}}$).
  - Also proved star-convexity of `CutPlane` from $0$ (`mul_mem_CutPlane_of_mem_Ioo`) and properties of `scaleW` (`scaleW_mem_UcDisk`, `zOfW_logRho`, `zOfW_scaleW`, `exp_re_scaleW_le`).
- [x] **Step 1.2 (Exact Cancellation of Higher Descendant Modes & Beta Integral)**:
  - Proved the Pochhammer cancellation identities `block1dCoeff_mul_pochhammer_div` and `block1dCoeff_mul_pochhammer_div_succ`, and deduced via `Finset.sum_comm` that all $m \ge 1$ descendant mode sums telescope (`sum_transmuteCoeff_eq`, `sum_transmuteCoeff_eq_zero`).
  - Defined `transmuteKernel`, `transmuteCore`, `transmuteCoreWeight` ($\frac{\Gamma(H - 1/2)}{\Gamma(H)}$), `transmuteWeight` ($(H - 1/2)\frac{\Gamma(H + 1/2)}{\Gamma(H)}$), and `transmute1d`, and evaluated the Beta integral `integral_betaKernel` via Mathlib's `Complex.betaIntegral`.
- [x] **Step 1.3 (Transmutation of `block1d`, $H$-Independent Operator `transmuteOp`, and Non-Negative Weights)**:
  - Proved `transmuteCore_block1d`, `transmuteCore_block1d_ofReal`, `transmute1d_block1d`, `integrableOn_transmuteKernel_mul_block1d`, and `transmuteCore_finset_sum_block1d`: for all $H > 1/2$ and $w \in \operatorname{UcDisk}$,
    $$\operatorname{transmuteCore}(\operatorname{block1d} H)\, w = \frac{\Gamma(H - 1/2)}{\Gamma(H)} \, e^{H w}.$$
  - Defined `derivHalfSub` and the $H$-independent differential-integral transmutation operator `transmuteOp f := derivHalfSub (derivHalfSub (transmuteCore f))` on `UcDisk`, and proved `transmuteOp_block1d` and `transmuteOp_finset_sum_block1d`.
  - Defined the non-negative measurable truncations `transmutePosWeight` and `transmuteCorePosWeight` (`measurable_transmutePosWeight`, `measurable_transmuteCorePosWeight`).

### Phase 2: Axiomatized Lightcone Block Decomposition (`LightconeBlockDecomp.lean`) — **Done (0 `sorry`s)**
- [x] **Step 2.1 (Action of `transmuteCore` and `transmuteOp` on `ConformalBlockLightcone`)**:
  - Proved `ConformalBlockLightconeLevel.transmuteCore_eval`, `ConformalBlockLightconeLevel.transmuteOp_eval`, `ConformalBlockLightcone.transmuteCore_evalLevel_zero`, `ConformalBlockLightcone.transmuteOp_evalLevel_zero`, and `ConformalBlockLightcone.exp_mul_transmuteOp_evalLevel_zero`.
- [x] **Step 2.2 (`LightconeBlockFourPointData` & Transmuted `MonomialFourPointData`)**:
  - Defined the Option A `LightconeBlockFourPointData` structure relating the 1D lightcone-block spectral measures $\mu^{\text{LC}}_J$ to the $d$-dimensional primary operator measures $\mu^{\text{prim}}_l$.
  - Constructed `toTransmutedMonomialFourPointData` via `Measure.withDensity` (`transmutedMeasure`) and proved `pairSpin_toTransmutedMonomialFourPointData`, `pairSpin_toTransmuted_eq_primary_of_support_leadingTwist`, and `primary_pair_eq_toTransmuted_pair_div`.

### Phase 3: Transmuted Crossing & Real-Axis Laplace Bound (`RealLaplaceBound.lean` & `TransmutedRealLaplace.lean`) — **Done (0 `sorry`s)**
- [x] **Step 3.1 (Mixed-Exponent Shifted Binomial Series & Transmuted $t$-Channel Identity)**:
  - Proved `summable_pochhammerCoeff_mixed_mul_exp` and `exists_uniform_bound_tsum_pochhammerCoeff_mixed_sub` in `RealLaplaceBound.lean` ($O(K^{-1})$ uniform convergence for mixed Pochhammer exponents $(a, b) = (2\Delta_\phi, 2\Delta_\phi + 1)$ valid for all $a > 0, b > 0$, unifying with the diagonal $a = b$ bound).
  - Defined `transmutedRatio`, `universalPrimaryLeadingCoeff` ($\frac{2 \cdot 4^{2\Delta_\phi}}{\Gamma(\Delta_\phi)^2}$), `transmutedUniversalLaplaceReal`, and `transmutedIdentityLaplaceReal` in `TransmutedRealLaplace.lean`, and proved `exists_uniform_bound_transmutedIdentityLaplaceReal_sub_universal` for **all $\Delta_\phi > 0$**.
- [x] **Step 3.2 (Uniform Real-Axis Laplace Bounds for All $\Delta_\phi > 0$)**:
  - Defined `LightconeBlockFourPointData.HasTransmutedCrossingGap` and proved `exists_uniform_transmuted_laplaceSpinReal_sub_identity_bounds` ($\alpha = \min(2 h_{\text{gap}},\, 2\Delta_\phi) > 0$) and `exists_uniform_transmuted_laplaceSpinReal_bounds` ($\alpha = \min(2 h_{\text{gap}},\, \min 1\, (2\Delta_\phi)) > 0$) on compact $[\sigma_-, \sigma_+] \subset (-\infty, 0)$ for **all $\Delta_\phi > 0$**.

### Phase 4: Quantitative Large-Spin Bootstrap for $d$-Dimensional Primary Operators (`PrimaryLargeSpin.lean`) — **Done (0 `sorry`s)**
- [x] **Step 4.1 (Transmuted Tauberian Theorems for All $\Delta_\phi > 0$)**:
  - Defined `transmutedUniversalPairing`, `transmutedUniversalShiftedMeasure`, `transmutedIdentityPairing`, `transmutedIdentityShiftedMeasure`, and `transmutedSpinShiftedMeasure`.
  - Applied `abs_integral_sub_le_of_laplaceReal_bound` (`LaplaceTauberian.lean`) to prove `exists_const_abs_transmuted_pairSpin_sub_identity_le` (and `_contDiff`, for all $\Delta_\phi > 0$ and $0 < \gamma < \min(2 h_{\text{gap}},\, 2\Delta_\phi)$) and `exists_const_abs_transmuted_pairSpin_sub_universal_le` (and `_contDiff`, for all $\Delta_\phi > 0$ and $0 < \gamma < \min(2 h_{\text{gap}},\, \min 1\, (2\Delta_\phi))$).
- [x] **Step 4.2 (Leading-Twist $d$-Dimensional Primary Bootstrap Theorems)**:
  - Combined the transmuted Tauberian theorems with `pairSpin_toTransmuted_eq_primary_of_support_leadingTwist`, `transmutedIdentityPairing_eq_of_support_leadingTwist`, and `transmutedUniversalPairing_eq_of_support_leadingTwist` to prove `exists_const_abs_primary_leadingTwist_sub_identity_le` (and `_contDiff`) and `exists_const_abs_primary_leadingTwist_sub_universal_le` (and `_contDiff`) for **all $\Delta_\phi > 0$ and $h_{\text{gap}} > 0$**.
