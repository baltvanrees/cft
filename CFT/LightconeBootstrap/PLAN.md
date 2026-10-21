# Quantitative Monomial Lightcone Bootstrap (Plan)

## 1. Goal & Mathematical Overview

This folder formalizes a **quantitative monomial lightcone bootstrap** with an explicit power-law error bound $O(J^{-\gamma})$ for compactly supported $C^2$ test functions $\varphi \in C_c^2(I)$ at large even spin $J = 2k$.

Compared to the qualitative Vitali + unbounded Fourier-inversion approach in `CFT/MonomialBootstrap/`, this pipeline is both **strictly stronger** (yielding a quantitative $O(J^{-\gamma})$ error rate controlled by the $t$-channel twist gap $h_{\text{gap}}$) and **architecturally simpler**: it requires only real-axis Laplace bounds from the CFT crossing equation, a bounded frequency window $t \in [-2\pi, 2\pi]$ via Nevanlinna's Two-Constants Theorem on a half-strip, and Fejér–Hermite interpolation on the double-twist lattice $\Delta_\phi + \mathbb{Z}$.

---

### Naming & Notation Conventions

To keep notation consistent with the rest of the repository (`CFT/Corr_pdisk.lean` and `CFT/MonomialBootstrap/`) and avoid symbol collisions:

| Symbol / Lean Name | Meaning | Notes |
|---|---|---|
| $w = \sigma + i t \in \operatorname{UcDisk}$ | Complex Laplace coordinate ($\sigma < 0$, $t \in \mathbb{R}$) | Matches $\sigma, t$ in `MonomialDecomp.lean` (avoids colliding with measures) |
| $h \in \mathbb{R}$, $u = h - h_0 \in \mathbb{R}$ | Twist variable $h$ and lattice-shifted twist $u$ ($h_0 = \Delta_\phi$) | Double-twist spectrum sits at $h \in \Delta_\phi + \mathbb{N}$, i.e. $u \in \mathbb{N} \subset \mathbb{Z}$ |
| $\mu, \nu$ | Positive measure $\mu$ and lattice-supported reference measure $\nu$ | Replaces $\sigma, \sigma_0$ so $\sigma$ remains reserved for $\operatorname{Re}(w)$ |
| $\mu_J$, $\mu_{\text{univ}}$ | Spin-$J$ CFT twist measure (`M.mu J`) and universal double-twist measure | Rescaled spin-$2k$ measure: $\tilde{\mu}_{2k} := (2k)^{1 - 2\Delta_\phi} \mu_{2k}$ |
| $K(u)$, $\widehat{K}(t)$ (`fejerKernel`, `fejerFourier`) | Fejér kernel $\bigl(\frac{\sin \pi u}{\pi u}\bigr)^2$ and triangle Fourier kernel $\frac{1}{2\pi}\bigl(1 - \frac{\|t\|}{2\pi}\bigr)_+$ | Avoids using $k$ for the Fourier kernel since $J = 2k$ is spin |
| $\alpha > 0$, $0 < \gamma < \alpha$ | Real-axis Laplace decay exponent $O(J^{-\alpha})$ and target exponent $O(J^{-\gamma})$ | Avoids confusing the decay rate exponent with twist $\tau$ |
| $\vartheta_A \in (0, 1)$ | Midpoint harmonic-measure factor $\frac{2}{\pi}\arctan\frac{1}{\sinh(\pi^2/(A-1))}$ | Approaches $1$ as the strip half-width parameter $A \to \infty$ |

---

### Key Mathematical Ingredients

1. **Fejér–Hermite Measure Estimate on $\mathbb{Z}$ (`HermiteMeasure.lean`)**:
   - Let $\mu, \nu$ be finite positive measures on $\mathbb{R}$ with $\operatorname{supp}(\nu) \subset \mathbb{Z}$ whose Fourier transforms differ by at most $\varepsilon$ on $[-2\pi, 2\pi]$:
     $$\left|\int_{\mathbb{R}} e^{i t u} \, d(\mu - \nu)(u)\right| \le \varepsilon \qquad (\forall t \in [-2\pi, 2\pi]).$$
   - **Step A (Quadratic lattice-distance bound from $t = 0, \pm 2\pi$)**:
     Since $\operatorname{dist}(u, \mathbb{Z})$ satisfies $8 \, \operatorname{dist}(u, \mathbb{Z})^2 \le 1 - \cos(2\pi u)$ and $1 - \cos(2\pi u)$ vanishes on $\mathbb{Z} \supset \operatorname{supp}(\nu)$, positivity of $\mu$ gives
     $$8 \int_{\mathbb{R}} \operatorname{dist}(u, \mathbb{Z})^2 \, d\mu(u) \le \int_{\mathbb{R}} (1 - \cos 2\pi u) \, d(\mu - \nu)(u) \le 2\varepsilon.$$
   - **Step B (Fejér–Hermite interpolant $H_\psi$)**:
     Set $K(u) := \bigl(\frac{\sin \pi u}{\pi u}\bigr)^2$. For any $\psi \in C_c^2(\mathbb{R})$ with $\operatorname{supp}(\psi) \subset [-B, B]$, define the finite sum
     $$H_\psi(u) := \sum_{n \in \mathbb{Z}} \bigl[\psi(n) + \psi'(n)(u - n)\bigr] K(u - n).$$
     1. *Bandlimited pairing bound*: The Fourier kernels of $K(u)$ and $u K(u)$ are $\widehat{K}(t) = \frac{1}{2\pi}\bigl(1 - \frac{|t|}{2\pi}\bigr)_+$ and $i \widehat{K}'(t)$, both supported in $[-2\pi, 2\pi]$ with $L^1$ norms $1$ and $1/\pi$. Hence
        $$\left|\int_{\mathbb{R}} H_\psi(u) \, d(\mu - \nu)(u)\right| \le \varepsilon \left(\sum_{n \in \mathbb{Z}} |\psi(n)| + \frac{1}{\pi}\sum_{n \in \mathbb{Z}} |\psi'(n)|\right).$$
     2. *Quadratic remainder bound*: At every integer $n \in \mathbb{Z}$, $H_\psi(n) = \psi(n)$ and $H_\psi'(n) = \psi'(n)$. Moreover, $\|K''\|_\infty \le 2\pi^2/3$ and $\|(u K)''\|_\infty \le 4\pi/3$, so $\|\psi'' - H_\psi''\|_\infty \le C_B \|\psi\|_{C^2}$. Taylor's theorem around a nearest integer yields
        $$\bigl|\psi(u) - H_\psi(u)\bigr| \le C_B \|\psi\|_{C^2} \, \operatorname{dist}(u, \mathbb{Z})^2 \qquad (\forall u \in \mathbb{R}).$$
     3. Since $\psi - H_\psi = 0$ on $\mathbb{Z}$, its integral against $\nu$ is zero, while Step A bounds its integral against $\mu$ by $\frac{1}{4} C_B \varepsilon \|\psi\|_{C^2}$, establishing the measure estimate:
        $$\left|\int_{\mathbb{R}} \psi(u) \, d(\mu - \nu)(u)\right| \le C_B \, \varepsilon \, \|\psi\|_{C^2}.$$

2. **Nevanlinna's Two-Constants Theorem on a Vertical Strip (`TwoConstants.lean`)**:
   - Let $E(\sigma + i t)$ be holomorphic on a vertical strip $\sigma_- \le \sigma \le \sigma_+ < 0$, uniformly bounded by $|E(\sigma + i t)| \le M$ on the strip, and bounded by $|E(\sigma)| \le \delta$ ($0 < \delta \le M$) on the real segment $[\sigma_-, \sigma_+]$.
   - On the upper/lower half-strips $[\sigma_-, \sigma_+] \times (0, \infty)$ and $[\sigma_-, \sigma_+] \times (-\infty, 0)$, the harmonic measure of the base segment $[\sigma_-, \sigma_+] \times \{0\}$ is given explicitly by
     $$\omega(\sigma, t) = \frac{2}{\pi} \arctan\!\left(\frac{\sin\bigl(\pi (\sigma - \sigma_-) / (\sigma_+ - \sigma_-)\bigr)}{\sinh\bigl(\pi |t| / (\sigma_+ - \sigma_-)\bigr)}\right).$$
   - Applying the maximum modulus principle on the truncated rectangle $[\sigma_-, \sigma_+] \times [0, T]$ and sending $T \to \infty$ gives the **Two-Constants bound**:
     $$\bigl|E(\sigma + i t)\bigr| \le M^{1 - \omega(\sigma, t)} \, \delta^{\omega(\sigma, t)} \qquad (\forall \sigma \in [\sigma_-, \sigma_+],\; \forall t \in \mathbb{R}).$$
   - Choosing $A > 1$, $[\sigma_-, \sigma_+] = [1 - 2A, -1]$, and evaluating at the midpoint $\sigma = -A$ on the frequency window $|t| \le 2\pi$ yields:
     $$\bigl|E(-A + i t)\bigr| \le M^{1 - \vartheta_A} \, \delta^{\vartheta_A} \qquad (|t| \le 2\pi),$$
     where the midpoint harmonic-measure exponent is
     $$\vartheta_A := \frac{2}{\pi} \arctan\!\left(\frac{1}{\sinh\bigl(\pi^2 / (A - 1)\bigr)}\right) \xrightarrow{A \to \infty} 1.$$

3. **Non-Asymptotic Laplace-to-$C_c^2$ Tauberian Estimate via Exponential Tilting (`LaplaceTauberian.lean`)**:
   - Before introducing any spin index $J$, combine `TwoConstants.lean` and `HermiteMeasure.lean` into a clean **single-pair non-asymptotic inequality**:
   - Let $\mu, \nu$ be positive measures on $\mathbb{R}$ with $\operatorname{supp}(\nu) \subset h_0 + \mathbb{Z}$. Suppose that for a given $A > 1$, their shifted real Laplace transforms on $[1 - 2A, -1]$ are bounded by $M_A / 2$ and differ by at most $\delta \in (0, M_A]$:
     $$\sup_{\sigma \in [1 - 2A, -1]} \left|\int_{\mathbb{R}} e^{\sigma(h - h_0)} \, d(\mu - \nu)(h)\right| \le \delta.$$
   - Tilting the shifted measures by $e^{-A u}$ ($u = h - h_0$) produces finite positive measures whose Fourier transform difference on $[-2\pi, 2\pi]$ is $E(-A + i t)$, bounded by $\varepsilon = M_A^{1 - \vartheta_A} \delta^{\vartheta_A}$.
   - Applying `HermiteMeasure.lean` to $\psi(u) := e^{A u}\varphi(h_0 + u)$ for any $\varphi \in C_c^2(I)$ gives the non-asymptotic bound:
     $$\left|\int_{\mathbb{R}} \varphi(h) \, d(\mu - \nu)(h)\right| \le C_{I, A} \, M_A^{1 - \vartheta_A} \, \delta^{\vartheta_A} \, \|\varphi\|_{C^2}.$$
   - **Asymptotic corollary**: If a sequence of measures $\mu_k, \nu_k$ has uniformly bounded Laplace moments on compact negative intervals and satisfies $\delta_k \le C (2k)^{-\alpha}$ ($\alpha > 0$), then for any $0 < \gamma < \alpha$, choosing $A > 1$ with $\alpha \vartheta_A \ge \gamma$ immediately gives
     $$\left|\int_{\mathbb{R}} \varphi(h) \, d(\mu_k - \nu_k)(h)\right| \le C_{I, \gamma} \, (2k)^{-\gamma} \, \|\varphi\|_{C^2}.$$

4. **Real-Axis Laplace Error Bound from $t$-Channel Crossing (`RealLaplaceBound.lean` & `QuantitativeLargeSpin.lean`)**:
   - For a crossing-symmetric four-point function with $t$-channel twist gap $h_{\text{gap}} > 0$, let $\tilde{\mu}_{2k} := (2k)^{1 - 2\Delta_\phi} \mu_{2k}$ be the normalized spin-$2k$ twist measure and let
     $$\mu_{\text{univ}} := \frac{2 \cdot 4^{2\Delta_\phi}}{\Gamma(2\Delta_\phi)} \sum_{n=0}^{\infty} \frac{(2\Delta_\phi)_n}{n!} \, \delta_{\Delta_\phi + n}$$
     be the universal double-twist reference measure supported on $\Delta_\phi + \mathbb{N} \subset \Delta_\phi + \mathbb{Z}$.
   - On every compact negative interval $[\sigma_-, \sigma_+] \subset (-\infty, 0)$, the real-axis Laplace difference satisfies
     $$\sup_{\sigma \in [\sigma_-, \sigma_+]} \left|\int_{\mathbb{R}} e^{\sigma h} \, d(\tilde{\mu}_{2k} - \mu_{\text{univ}})(h)\right| \le C_{[\sigma_-, \sigma_+]} \, (2k)^{-\alpha},$$
     with $\alpha = \min(2 h_{\text{gap}},\, 1,\, 2\Delta_\phi - 1)$ against $\mu_{\text{univ}}$ (or $\alpha = 2 h_{\text{gap}}$ against the exact $t$-channel identity measure $\mu_{\text{id}, 2k}$ when using a piecewise/curved $\theta$-contour so that $|\theta| \ge \pi/4$ is exponentially suppressed for all $\Delta_\phi > 0$).
   - Applying `LaplaceTauberian.lean` yields the quantitative lightcone bootstrap theorem for all $\varphi \in C_c^2(I)$ and $0 < \gamma < \alpha$.

---

## 2. Folder & File Structure

Standalone mathematical analysis modules are placed in `CFT/Analysis/`, while the CFT lightcone bootstrap pipeline resides in `CFT/LightconeBootstrap/`:

```text
CFT/Analysis/
  ├── DominatedHolomorphy.lean    (Cauchy Fréchet derivative bounds & dominated integral/tsum holomorphy)
  ├── Vitali.lean                 (Equicontinuity & real-interval Vitali–Porter convergence theorems)
  ├── HermiteMeasure.lean         (Fejér kernel K, Hermite interpolant H_ψ, & C_c^2 lattice measure estimate)
  ├── TwoConstants.lean           (Half-strip harmonic measure ω(σ, t) & Nevanlinna's Two-Constants Theorem)
  └── LaplaceTauberian.lean       (Non-asymptotic & power-law Laplace-to-C_c^2 Tauberian theorems via tilting)

CFT/Corr_pdisk.lean  (two-variable crossing symmetry `crossing_correlator` — 0 sorry's)
       │
       ▼
CFT/LightconeBootstrap/
  ├── PLAN.md
  ├── MonomialDecomp.lean         (MonomialFourPointData, canonical map, & folded spin-J Fourier projection)
  ├── Gap.lean                    (Twist gap & t-channel identity dominance)
  ├── RealLaplaceBound.lean       (Uniform O((2k)^{-α}) real-axis Laplace error bounds on compact [σ_-, σ_+])
  └── QuantitativeLargeSpin.lean  (Main quantitative lightcone bootstrap theorems for C_c^2 test functions)
```

`CFT/Analysis/` contains **pure analysis modules** with no dependency on CFT definitions.

---

## 3. Step-by-Step Implementation Plan

### Phase 1: Pure Analysis Engine — **Done (0 `sorry`s)**

#### Step 1: `CFT/Analysis/HermiteMeasure.lean` — **Done (0 `sorry`s)**
- [x] **Lattice distance & trigonometric lower bound**:
  - Define `distInt (u : ℝ) : ℝ := |u - round u|` and prove `distInt u ≤ 1 / 2`, `distInt (n : ℝ) = 0`, and `8 * (distInt u)^2 ≤ 1 - Real.cos (2 * π * u)` for all $u \in \mathbb{R}$.
  - Prove the quadratic concentration bound (`eight_mul_integral_distInt_sq_le`): for any finite positive measure $\mu$ and finite measure $\nu$ supported on $\mathbb{Z}$ with $|\widehat{\mu}(t) - \widehat{\nu}(t)| \le \varepsilon$ for $t \in \{0, 2\pi, -2\pi\}$,
    $$8 \int_{\mathbb{R}} \operatorname{dist}(u, \mathbb{Z})^2 \, d\mu(u) \le \int_{\mathbb{R}} (1 - \cos 2\pi u) \, d\mu(u) \le 2\varepsilon.$$
- [x] **Fejér kernel $K(u)$ and its Fourier representation**:
  - Define `fejerKernel (u : ℝ) : ℝ` and `fejerSlopeKernel (u : ℝ) : ℝ` via their $[0, 2\pi]$ Fourier integrals and prove closed-form identities $K(u) = \bigl(\frac{\sin \pi u}{\pi u}\bigr)^2$ and $u K(u)$.
  - Deduce $K \in C^2(\mathbb{R})$, $u K \in C^2(\mathbb{R})$, the interpolation values at $m \in \mathbb{Z}$:
    $$K(0) = 1,\quad K'(0) = 0,\quad (u K)(0) = 0,\quad (u K)'(0) = 1,$$
    $$K(m) = K'(m) = (u K)(m) = (u K)'(m) = 0 \quad (\forall m \in \mathbb{Z} \setminus \{0\}),$$
    and the uniform second-derivative bounds $\|K''\|_\infty \le 2\pi^2/3$ and $\|(u K)''\|_\infty \le 4\pi/3$.
- [x] **Hermite interpolant $H_\psi$ and $C_c^2$ measure estimate**:
  - For $\psi \in C_c^2(\mathbb{R})$ with $\operatorname{supp}(\psi) \subset [-N, N]$, define the finite sum `hermiteInterp N ψ`:
    $$H_\psi(u) = \sum_{n \in \mathbb{Z} \cap [-N, N]} \bigl[\psi(n) K(u - n) + \psi'(n) (u - n) K(u - n)\bigr].$$
  - Prove the bandlimited pairing bound (`abs_integral_hermiteInterp_sub_le`):
    $$\left|\int_{\mathbb{R}} H_\psi(u) \, d(\mu - \nu)(u)\right| \le \varepsilon \left(\sum_{n} |\psi(n)| + \frac{1}{\pi} \sum_{n} |\psi'(n)|\right) \le C_{1, N} \, \varepsilon \, \|\psi\|_{C^2}.$$
  - Prove $H_\psi(n) = \psi(n)$ and $H_\psi'(n) = \psi'(n)$ for all $n \in \mathbb{Z}$, bound $\|(\psi - H_\psi)''\|_\infty \le C_{2, N} \|\psi\|_{C^2}$, and apply second-order Taylor's theorem at the nearest integer `round u` (`abs_le_mul_distInt_sq_of_vanish_on_int`) to obtain:
    $$\bigl|\psi(u) - H_\psi(u)\bigr| \le C_N \|\psi\|_{C^2} \, \operatorname{dist}(u, \mathbb{Z})^2.$$
  - Combine the bandlimited and remainder bounds to prove `abs_integral_sub_le_of_fourier_bound` and `abs_integral_sub_le_of_fourier_bound_contDiff`.

#### Step 2: `CFT/Analysis/TwoConstants.lean` — **Done (0 `sorry`s)**
- [x] **Harmonic measure on the half-strip $[\sigma_-, \sigma_+] \times (0, \infty)$**:
  - For $\sigma_- < \sigma_+$, define `stripHarmonicMeasure`:
    $$\omega(\sigma, t) = \frac{2}{\pi} \arctan\!\left(\frac{\sin\bigl(\pi (\sigma - \sigma_-) / (\sigma_+ - \sigma_-)\bigr)}{\sinh\bigl(\pi |t| / (\sigma_+ - \sigma_-)\bigr)}\right).$$
  - Verify that $\omega(\sigma, t)$ is the real part of the explicit holomorphic function `harmonicMajorantHolomorphic` on the open half-strip, satisfies $0 \le \omega(\sigma, t) \le 1$, vanishes on the vertical sides $\sigma = \sigma_\pm$ ($t \ne 0$), and satisfies $\sup_{\sigma \in [\sigma_-, \sigma_+]} \omega(\sigma, T) \to 0$ as $T \to \infty$.
- [x] **Nevanlinna's Two-Constants Theorem on the vertical strip**:
  - Prove `norm_le_two_constants_vertical_strip`: for any function $E(w)$ holomorphic on the open strip $\sigma_- < \operatorname{Re}(w) < \sigma_+$ and continuous on the closed strip $\sigma_- \le \operatorname{Re}(w) \le \sigma_+$ satisfying $|E(\sigma + i t)| \le M$ on the strip and $|E(\sigma)| \le \delta$ ($0 < \delta \le M$) on the real segment $\sigma \in [\sigma_-, \sigma_+]$,
    $$\bigl|E(\sigma + i t)\bigr| \le M^{1 - \omega(\sigma, t)} \, \delta^{\omega(\sigma, t)} \qquad (\forall \sigma \in [\sigma_-, \sigma_+],\; \forall t \in \mathbb{R}).$$
- [x] **Midpoint specialization on $[1 - 2A, -1]$ for $|t| \le T$**:
  - Define `midpointHarmonicExp A T` ($\vartheta_{A, T} := \frac{2}{\pi} \arctan\bigl(1 / \sinh(\pi T / (2(A - 1)))\bigr)$) for $A > 1, T > 0$ and prove $\vartheta_{A, T} \in (0, 1)$ and `tendsto_midpointHarmonicExp_atTop` ($\lim_{A \to \infty} \vartheta_{A, T} = 1$).
  - Prove `norm_le_midpoint_two_constants`: if $|E(\sigma)| \le \delta$ on $[1 - 2A, -1]$ and $|E(\sigma + i t)| \le M$ on $[1 - 2A, -1] \times \mathbb{R}$, then for all $|t| \le T$:
    $$\bigl|E(-A + i t)\bigr| \le M^{1 - \vartheta_{A, T}} \, \delta^{\vartheta_{A, T}}.$$

#### Step 3: `CFT/Analysis/LaplaceTauberian.lean` — **Done (0 `sorry`s)**
- [x] **Single-pair non-asymptotic Laplace-to-$C_c^2$ bound**:
  - Prove `abs_integral_sub_le_of_laplaceReal_bound` and `abs_integral_sub_le_of_laplaceReal_bound_contDiff`: given positive measures $\mu, \nu$ with $\operatorname{supp}(\nu) \subset \mathbb{Z}$ whose Laplace transforms on $[1 - 2A, -1]$ ($A > 1$) satisfy $L_\mu(\sigma) + L_\nu(\sigma) \le M$ and $|L_\mu(\sigma) - L_\nu(\sigma)| \le \delta \in (0, M]$, tilting by $e^{-A u}$ (`tiltedMeasure A`) and combining `TwoConstants.lean` with `HermiteMeasure.lean` yields:
    $$\left|\int_{\mathbb{R}} \varphi(u) \, d(\mu - \nu)(u)\right| \le C_{N, A} \, M^{1 - \vartheta_A} \, \delta^{\vartheta_A} \, \|\varphi\|_{C^2}.$$
- [x] **Power-law asymptotic corollary**:
  - Prove `exists_const_abs_integral_sub_le_rpow`: for any $0 < \gamma < \alpha$, choosing $A > 1$ with $\alpha \vartheta_A \ge \gamma$ yields
    $$\left|\int_{\mathbb{R}} \varphi(u) \, d(\mu - \nu)(u)\right| \le C_{N, \gamma} \, J^{-\gamma} \, \|\varphi\|_{C^2}.$$

---

### Phase 2: CFT Real-Axis Laplace Bounds & Main Quantitative Bootstrap Theorem — **Done (0 `sorry`s)**

#### Step 4: Lift `MonomialDecomp.lean` and `Gap.lean` — **Done (0 `sorry`s)**
- [x] Lift `MonomialFourPointData`, its canonical construction `FourPointData.toMonomialFourPointData`, the folded spin-$J$ Fourier projection on $[-\pi/2, \pi/2]$ (`laplaceSpinReal_eq_fourierProjSpin`), `HasTwistGap`, and the $t$-channel identity dominance bound (`norm_eval_sub_crossIdentity_le`).

#### Step 5: `CFT/LightconeBootstrap/RealLaplaceBound.lean` — **Done (0 `sorry`s)**
- [x] **Uniform real-axis Laplace error bound on compact negative intervals $[\sigma_-, \sigma_+]$**:
  - Upgrade the pointwise real-axis bounds in `MonomialBootstrap/IdentityProj.lean` and `MonomialBootstrap/LargeSpin.lean` to **uniform** $O((2k)^{-\alpha})$ bounds over $\sigma \in [\sigma_-, \sigma_+] \subset (-\infty, 0)$:
    1. Against the exact finite-spin $t$-channel identity Laplace transform `identityLaplaceReal Δ_phi (2k) σ` (retaining all $1/(2k)^m$ subleading binomial coefficients $\frac{(2\Delta_\phi)_{n+2k}}{(n+2k)!}$ so that the $O((2k)^{-1})$ Gamma-limit error is absent), with $\alpha = \min(2 h_{\text{gap}},\, 2\Delta_\phi - 1)$ (`MonomialFourPointData.exists_uniform_laplaceSpinReal_sub_identity_bounds`):
       $$\sup_{\sigma \in [\sigma_-, \sigma_+]} (2k)^{1 - 2\Delta_\phi} \Bigl|L_{2k}(\sigma) - L_{\text{id}, 2k}(\Delta_\phi, \sigma)\Bigr| \le C_{[\sigma_-, \sigma_+]} \, (2k)^{-\min(2 h_{\text{gap}},\, 2\Delta_\phi - 1)}.$$
    2. Against the asymptotic $J \to \infty$ double-twist Laplace transform $L_{\text{id}}(\Delta_\phi, \sigma)$ (`universalLaplaceReal Δ_phi σ`), with $\alpha = \min(2 h_{\text{gap}},\, 1,\, 2\Delta_\phi - 1)$ (`MonomialFourPointData.exists_uniform_laplaceSpinReal_bounds`).
  - *(Optional refinement)*: Using a piecewise/curved $\theta$-contour that stays at $\operatorname{Re}(w_r) = \sigma_+/2 < 0$ for $|\theta| \in [\pi/4, \pi/2]$ and shifts to $\operatorname{Re}(w_r) = -1/(2k)$ only for $|\theta| \le \pi/4$, eliminate the $(2k)^{1 - 2\Delta_\phi}$ endpoint artifact so that comparing against the exact $t$-channel identity measure $\mu_{\text{id}, 2k}$ yields the **pure twist-gap exponent $\alpha = 2 h_{\text{gap}}$ for all $\Delta_\phi > 0$**.

#### Step 6: `CFT/LightconeBootstrap/QuantitativeLargeSpin.lean` — **Done (0 `sorry`s)**
- [x] Combine `LaplaceTauberian.lean` with `RealLaplaceBound.lean` to prove the **main quantitative monomial lightcone bootstrap theorems**:
  1. **Against the exact finite-spin $t$-channel identity pairing** (`MonomialFourPointData.exists_const_abs_pairSpin_sub_identity_le`, `MonomialFourPointData.exists_const_abs_pairSpin_sub_identity_le_contDiff`, and `FourPointData.exists_const_abs_pairSpin_sub_identity_le`):
     For every compact interval $I \subset \mathbb{R}$ and every $0 < \gamma < \min(2 h_{\text{gap}},\, 2\Delta_\phi - 1)$, there exists $C_{I, \gamma} > 0$ such that for all $\varphi \in C_c^2(I)$ and all $k \ge 1$:
     $$(2k)^{1 - 2\Delta_\phi} \left|\int_{\mathbb{R}} \varphi(h) \, d\mu_{2k}(h) - 2 \cdot 4^{2\Delta_\phi} \sum_{n=0}^{\infty} \frac{(2\Delta_\phi)_n}{n!} \frac{(2\Delta_\phi)_{n + 2k}}{(n + 2k)!} \, \varphi(\Delta_\phi + n)\right| \le C_{I, \gamma} \, (2k)^{-\gamma} \, \|\varphi\|_{C^2}.$$
  2. **Against the asymptotic $J \to \infty$ universal pairing** (`MonomialFourPointData.exists_const_abs_pairSpin_sub_universal_le`, `MonomialFourPointData.exists_const_abs_pairSpin_sub_universal_le_contDiff`, and `FourPointData.exists_const_abs_pairSpin_sub_universal_le`):
     For every $0 < \gamma < \min(2 h_{\text{gap}},\, 1,\, 2\Delta_\phi - 1)$,
     $$\left|(2k)^{1 - 2\Delta_\phi} \int_{\mathbb{R}} \varphi(h) \, d\mu_{2k}(h) - \frac{2 \cdot 4^{2\Delta_\phi}}{\Gamma(2\Delta_\phi)} \sum_{n=0}^{\infty} \frac{(2\Delta_\phi)_n}{n!} \, \varphi(\Delta_\phi + n)\right| \le C_{I, \gamma} \, (2k)^{-\gamma} \, \|\varphi\|_{C^2}.$$
