# Plan: Eliminating `HasTransmutedCrossing` by Formalizing the Convergent Inner-Derivative Transmutation Proof

## 1. Goal & Overview

In the current codebase (`CFT/LightconeBootstrap/TransmutedRealLaplace.lean` and `PrimaryLargeSpin.lean`), the quantitative transmuted lightcone bootstrap for all $\Delta_\phi > 0$ and $0 < \gamma < \min(2 h_{\mathrm{gap}},\, 2\Delta_\phi)$ rests on two assumptions (`Assumption 2` in `doc/monomial_bootstrap.tex`):
1. **Collinear block decomposition (`LightconeBlockFourPointData` in `LightconeBlockDecomp.lean`)**: the $s$-channel correlator $\mathcal{G}(w_l, w_r)$ expands in 1D collinear blocks $e^{h w_l} k_{h + J}(e^{w_r})$ with positive spectral measures $\mu^{\mathrm{LC}}_J$ (matching $C_{0, \ell} \mu^{\mathrm{prim}}_\ell$ on $(-\infty, h_{\mathrm{gap}} + 1)$).
2. **Pointwise transmuted $t$-channel crossing (`HasTransmutedCrossing` in `TransmutedRealLaplace.lean`)**: applying the 1D fractional transmutation operator $\mathcal{L}_0$ to the right coordinate $w_r$ produces the leading transmuted $t$-channel identity $\mathcal{C}_{\Delta_\phi}(w_l) \mathcal{C}^{\mathrm{trans}}_{\Delta_\phi}(w_r)$ up to a $t$-channel twist-gap remainder $O\bigl(e^{h_{\mathrm{gap}} \operatorname{Re} w_r'}\bigr)$.

**Goal of this plan**: Eliminate Assumption 2.2 (`HasTransmutedCrossing`) **entirely**—proving the real-axis transmuted Laplace bound `HasTransmutedCrossingGap` directly from the base Euclidean/polydisk crossing axioms (`FourPointData` in `Corr.lean` / `Corr_pdisk.lean`) and the $s$-channel collinear block decomposition (`LightconeBlockFourPointData`), **without introducing any $O(k^{-1})$ error** and preserving the full exponent range
$$0 < \gamma < \min\bigl(2 h_{\mathrm{gap}},\, 2\Delta_\phi\bigr) \qquad (\forall \Delta_\phi > 0,\; h_{\mathrm{gap}} > 0).$$

This plan follows Section 3.1, Section 5, and Appendix A of the consolidated research notes (*The scalar lightcone bootstrap at fixed spin*, 25 September 2026), specialized to identical scalars ($\delta = 0$, $a = \Delta_\phi$, $p = s = 2\Delta_\phi$).

---

## 2. Key Mathematical Simplifications at $\delta = 0$ (Identical Scalars)

In the general unequal-scalar case ($\delta = \frac{\Delta_2 - \Delta_1}{2} \ge 0$), the convergent inner-derivative transmutation operator $\mathcal{L}_\delta$ in Equations (5.4) and (A.9) involves two hypergeometric kernels $U(t) = {}_2F_1(\delta, \delta; 2\delta + 1/2; 1 - t)$ and $V(t) = {}_2F_1(\delta - 1/2, \delta + 1/2; 2\delta + 1/2; 1 - t)$.

For **identical scalars ($\delta = 0$, $b = 1/2$)**, a major simplification occurs (Appendix A.1, p. 17):
1. **No hypergeometric kernels in $\mathcal{L}_0$**:
   At $\delta = 0$, $U(t) \equiv 1$ and $V(t) \equiv \sqrt{t} = \frac{\sqrt{x}(1 + q)}{1 + qx}$ ($q = e^{w_r}$, $v = qx = e^{w_r + \log x}$). Consequently, the kernels $K_A(q, x)$ and $K_B(q, x)$ in (A.10)–(A.11) are **purely elementary**:
   $$K_A(q, x) = \frac{1}{\sqrt{\pi}} x^{-1/2}(1 - x)^{-1/2}(1 - q^2 x)^{-1/2} \frac{(1 + q)^2 (1 - qx)}{1 + qx},$$
   $$K_B(q, x) = \frac{4q}{(1 + q)^2} K_A(q, x) = Z(q) \, K_A(q, x).$$
2. **Exact algebraic second-order cancellation at $q = 1$**:
   Because $V(t) - \sqrt{t} U(t) \equiv 0$ at $\delta = 0$, Equation (A.18) simplifies to the exact algebraic identity
   $$K_A(q, x) - K_B(q, x) = \bigl(1 - Z(q)\bigr) K_A(q, x) = \left(\frac{1 - q}{1 + q}\right)^2 K_A(q, x).$$
3. **Cancellation of the $1 + qx$ denominator**:
   In terms of $w_r \in \operatorname{UcDisk}$ ($q = e^{w_r}$, $v = x e^{w_r} = e^{w_r + \log x}$), the radial Euler operator is $\mathscr{D} = \frac{v(1 + v)}{1 - v} \partial_v = \frac{1 + x e^{w_r}}{1 - x e^{w_r}} \partial_{w_r}$. Substituting $K_A$ and $K_B$ into (A.9), both the $(1 + q)^2$ factor and the $1 + qx$ denominator cancel against $\mathscr{D}$:
   $$\frac{1 - v}{1 + v} \mathscr{D} F = \partial_{w_r} F, \qquad \frac{1 - v}{1 + v} \mathscr{D}^2 F = \partial_{w_r}\!\left(\frac{1 + x e^{w_r}}{1 - x e^{w_r}} \partial_{w_r} F\right).$$
   Thus the inner-derivative transmutation operator at $\delta = 0$ takes the completely explicit form:
   $$\boxed{\bigl(\mathcal{L}_0 f\bigr)(w_r) = \frac{1}{\sqrt{\pi}} \int_0^1 x^{-1/2}(1 - x)^{-1/2}\bigl(1 - x e^{2 w_r}\bigr)^{-1/2} \, \mathcal{D}_{\mathrm{inner}}(w_r, x, f) \, dx}$$
   where
   $$\mathcal{D}_{\mathrm{inner}}(w_r, x, f) := (1 - e^{w_r})^2 \left[\frac{1 + x e^{w_r}}{1 - x e^{w_r}} f''(w_r + \log x) + \frac{2 x e^{w_r}}{(1 - x e^{w_r})^2} f'(w_r + \log x)\right] - \frac{1}{2}(1 + e^{w_r})^2 f'(w_r + \log x).$$
4. **Why this solves both endpoint problems simultaneously**:
   - **At $x \to 0^+$ (low weight / $s$-channel vacuum)**: Because $\mathcal{D}_{\mathrm{inner}}$ only involves $f'$ and $f''$, the $s$-channel identity $f \equiv 1$ is **annihilated identically** ($\mathcal{D}_{\mathrm{inner}}(w_r, x, 1) = 0$) before integrating. Moreover, the kernel at $x = 0$ is $x^{-1/2}$ (rather than $x^{-3/2}$), which is integrable for all $H \ge 0$.
   - **Near $q = e^{w_r} \to 1$ ($t$-channel endpoint)**: The $(1 - e^{w_r})^2$ factor in front of the second-derivative term in $\mathcal{D}_{\mathrm{inner}}$ provides the exact two powers of $u = |1 - e^{w_r}| + (1 - x)$ needed to compensate the two extra inverse powers of $u$ from differentiating the $t$-channel remainder twice.

---

## 3. Architecture & File Breakdown

To keep builds fast and files modular, the implementation is divided into 5 stages across existing and new files in `CFT/LightconeBootstrap/`:

```text
CFT/LightconeBootstrap/
  ├── Transmute1d.lean                (Stage 1: Add inner-derivative operator `transmuteOpInner`,
  │                                    equivalence with `transmuteOp` for H > 1/2, extension to H ≥ 0)
  ├── LightconeBlockDecomp.lean       (Stage 2: Link `LightconeBlockFourPointData` to `FourPointData`
  │                                    and prove termwise commutation of `transmuteOpInner` with OPE)
  ├──ExactTransmutedRef.lean         (Stage 3 [NEW]: Exact 1D GFF block coefficients c_m, exact
  │                                    transformed reference S_0(q) and M_J^0, 0-error Laplace identity)
  ├── TransmutedEndpointBounds.lean   (Stage 4 [NEW]: Split x ∈ (0, x_0] vs [x_0, 1), kernel derivative
  │                                    bounds at q = ±1, and N-fold IBP contour lemma (Lemma 3.1))
  ├── TransmutedRealLaplace.lean      (Stage 5: Derive `HasTransmutedCrossingGap` from Stages 2–4)
  └── PrimaryLargeSpin.lean           (Stage 5: Unconditional Theorem 2 without `HasTransmutedCrossing`)
```

---

## 4. Detailed Step-by-Step Implementation Plan

### Stage 1: Inner-Derivative Transmutation Operator (`Transmute1d.lean`)

1. **Step 1.1 — Definition of `eulerD` ($\mathscr{D}_w$) and `transmuteInnerDiff` ($\mathcal{D}_{\mathrm{inner}}$)**:
   - Define the radial Euler derivative on $\operatorname{UcDisk}$:
     ```lean
     noncomputable def eulerD (f : ℂ → ℂ) (w : ℂ) : ℂ :=
       (1 + Complex.exp w) / (1 - Complex.exp w) * deriv f w
     ```
   - Define `transmuteInnerKernel (w : ℂ) (x : ℝ) : ℂ`:
     $$K_{\mathrm{inner}}(w, x) := x^{-1/2}(1 - x)^{-1/2}\bigl(1 - x e^{2w}\bigr)^{-1/2}$$
     and `transmuteInnerDiff (f : ℂ → ℂ) (w : ℂ) (x : ℝ) : ℂ`:
     $$\mathcal{D}_{\mathrm{inner}}(w, x, f) := (1 - e^w)^2 \left[\frac{1 + x e^w}{1 - x e^w} (\operatorname{deriv}^2 f)(w + \log x) + \frac{2 x e^w}{(1 - x e^w)^2} (\operatorname{deriv} f)(w + \log x)\right] - \frac{1}{2}(1 + e^w)^2 (\operatorname{deriv} f)(w + \log x).$$
   - Define `transmuteOpInner (f : ℂ → ℂ) (w : ℂ) : ℂ`:
     $$\operatorname{transmuteOpInner}(f)(w) := \frac{1}{\sqrt{\pi}} \int_{x \in (0, 1)} K_{\mathrm{inner}}(w, x) \, \mathcal{D}_{\mathrm{inner}}(w, x, f) \, dx.$$
   - Prove `transmuteInnerDiff_const` and `transmuteOpInner_const`: $\operatorname{transmuteOpInner}(\text{const}) = 0$ (annihilates the $s$-channel identity $k_0 = 1$).

2. **Step 1.2 — Agreement with `transmuteOp` on `block1d H` ($H > 0$)**:
   - Using $\partial_w [f(w + \log x)] = x \partial_x [f(w + \log x)]$ and integration by parts on $(0, 1)$ (or directly evaluating the Beta integral on each mode $e^{(H + 2n) w}$ via $(H - 1/2) \operatorname{Beta}(H - 1/2, 1/2) = \operatorname{Beta}(H + 1/2, 1/2)$), prove that for all $H > 0$ and $w \in \operatorname{UcDisk}$:
     $$\operatorname{transmuteOpInner}(\operatorname{block1d} H)\, w = \operatorname{transmuteWeight}(H) \, e^{H w}.$$
   - In particular, for $H > 1/2$, `transmuteOpInner (block1d H) w = transmuteOp (block1d H) w`, while `transmuteOpInner` extends the identity to all $0 < H \le 1/2$ and $H = 0$ (`block1d 0 = 1`).

---

### Stage 2: Termwise Transmutation of the $s$-Channel Correlator (`LightconeBlockDecomp.lean`)

1. **Step 2.1 — Connecting `LightconeBlockFourPointData` to `FourPointData`**:
   - Add a structure or predicate `LightconeBlockFourPointData.AgreesWithCorrelator (corr : FourPointData ν Δ_phi)` stating that for all $(w_l, w_r) \in \operatorname{UcPdisk}$,
     $$\text{corr.correlator\_pdisk}(w_l, w_r) = 1 + \sum_{J \in \mathbb{Z}} \int_{[0, \infty)} e^{h w_l} \, \operatorname{block1d}(h + J, w_r) \, d\mu^{\mathrm{LC}}_J(h),$$
     with normal majorant convergence on $\operatorname{Re} w_l \le \sigma_l < 0$, $\operatorname{Re} w_r \le \sigma_r < 0$:
     $$\sum_{J \in \mathbb{Z}} \int_{[0, \infty)} e^{h \sigma_l + (h + J)\sigma_r} \, d\mu^{\mathrm{LC}}_J(h) < \infty$$
     and non-identity twist gap $\mu^{\mathrm{LC}}_J\bigl((-\infty, h_{\mathrm{gap}})\bigr) = 0$.

2. **Step 2.2 — Commuting `transmuteOpInner` with the $s$-Channel Sum/Integral**:
   - Using Cauchy derivative bounds on $\operatorname{block1d}(H, w_r + \log x)$ for $\operatorname{Re} w_r \le \sigma_r < 0$ (absorbed by a slightly larger radial modulus $\sigma_r / 2 < 0$) and the $O(x^{h_{\mathrm{gap}} - 1/2})$ integrable majorant at $x \to 0^+$, apply Fubini's theorem (`integral_integral_swap` / `hasSum_integral_of_dominated_convergence`) to prove:
     $$\operatorname{transmuteOpInner}\bigl(\text{corr.correlator\_pdisk } w_l\bigr)(w_r) = L.\text{toTransmutedMonomialFourPointData.eval } w_l\, w_r.$$

---

### Stage 3: Exact Transformed Reference $S_0(q)$ and $M_J^0$ (`ExactTransmutedRef.lean`)

1. **Step 3.1 — Exact 1D GFF Collinear Block Expansion of $\mathcal{C}_{\Delta_\phi}(w_r)$ (Section 5.3, Equations (5.19)–(5.23))**:
   - Define the 1D GFF block coefficients (Equation (2.15) at $\delta = 0$, $\Delta_1 = \Delta_2 = \Delta_\phi$, $p = 2\Delta_\phi$):
     $$c_m(\Delta_\phi) := 4^{\Delta_\phi + m} \frac{(\Delta_\phi)_m^2}{m! \, (2\Delta_\phi + m - 1)_m} \qquad (c_0 = 4^{\Delta_\phi})$$
     and the exact transmuted reference coefficients $\mathfrak{m}_m(\Delta_\phi) := w_0(\Delta_\phi + m) \, c_m(\Delta_\phi)$ (Equation (5.21)–(5.22)):
     $$\mathfrak{m}_m(\Delta_\phi) = \frac{4^{\Delta_\phi} \Gamma(2\Delta_\phi + 1)}{\Gamma(\Delta_\phi)^2} \left[\frac{(2\Delta_\phi + 1)_m}{m!} - \frac{(2\Delta_\phi)_m}{m!} + \frac{\Delta_\phi - 1/2}{4\Delta_\phi} \frac{(2\Delta_\phi - 1)_m}{m!}\right].$$
   - Prove the exact closed-form summation of $S_0(w_r) := \sum_{m=0}^\infty \mathfrak{m}_m(\Delta_\phi) e^{(\Delta_\phi + m) w_r}$ on $\operatorname{UcDisk}$:
     $$S_0(w_r) = \mathcal{C}^{\mathrm{trans}}_{\Delta_\phi}(w_r) \left[1 - (1 - e^{w_r}) + \frac{\Delta_\phi - 1/2}{4\Delta_\phi}(1 - e^{w_r})^2\right] = \operatorname{transmuteOpInner}\bigl(\operatorname{crossFactor} \Delta_\phi\bigr)(w_r).$$
   - Note that every term in $\mathfrak{m}_m(\Delta_\phi)$ is a linear combination of three shifted Pochhammer coefficients $\operatorname{pochhammerCoeff}(2\Delta_\phi + 1, m)$, $\operatorname{pochhammerCoeff}(2\Delta_\phi, m)$, and $\operatorname{pochhammerCoeff}(2\Delta_\phi - 1, m)$, so:
     - For $m \ge 1$ and $\Delta_\phi > 0$, $\mathfrak{m}_m(\Delta_\phi) > 0$ (Equation (5.22)).
     - At large spin $m = n + 2k$, the subleading two terms are $O(k^{-1})$ and $O(k^{-2})$ relative to the leading term $\frac{(2\Delta_\phi + 1)_{n+2k}}{(n+2k)!}$, so the kinematic large-$k$ expansion `exists_const_abs_transmutedIdentityPairing_sub_universal_le` to `transmutedUniversalPairing` still holds with $O(k^{-1})$ error!

2. **Step 3.2 — Exact Finite-Spin Reference Measure $M_{2k}^0$ (Equation (5.28))**:
   - Update `transmutedIdentityLaplaceReal` and `transmutedIdentityPairing` to use $\mathfrak{m}_{n + 2k}(\Delta_\phi)$ (or provide `exactTransmutedIdentityPairing` alongside `transmutedIdentityPairing`, since their difference is $O(k^{-1})$):
     $$\operatorname{exactTransmutedIdentityPairing}(\Delta_\phi, 2k, \varphi) := 2 \cdot 4^{\Delta_\phi} \sum_{n=0}^{\infty} \frac{(2\Delta_\phi)_n}{n!} \, \mathfrak{m}_{n + 2k}(\Delta_\phi) \, \varphi(\Delta_\phi + n).$$
   - Because $\mathfrak{m}_{n + 2k}(\Delta_\phi)$ is the **exact** Fourier coefficient of $\operatorname{transmuteOpInner}(\operatorname{crossFactor} \Delta_\phi)$, subtracting $S_0(w_r)$ from the transmuted $t$-channel identity leaves **zero** $t$-channel identity remainder—avoiding any $O(1 - e^{w_r})$ or $O(k^{-1})$ truncation error!

---

### Stage 4: Split-Interval Kernel Estimates & Localized Angular Integration by Parts (`TransmutedEndpointBounds.lean`)

1. **Step 4.1 — Splitting $x \in (0, x_0]$ ($s$-Channel Bound) vs. $x \in [x_0, 1)$ ($t$-Channel Bound) (Section 5.2 & Appendix A.3–A.5)**:
   - Fix $x_0 = 1/2$. Split the integral defining $\operatorname{transmuteOpInner}(R(w_l, \cdot))(w_r)$ into:
     - **Low-$x$ part $x \in (0, 1/2]$**:
       Write $R(w_l, w_r + \log x) = \bigl(\mathcal{G}(w_l, w_r + \log x) - 1\bigr) - \bigl(\operatorname{crossIdentity}(\Delta_\phi, w_l, w_r + \log x) - 1\bigr)$.
       Since $\mathcal{D}_{\mathrm{inner}}$ annihilates $1$ and $\operatorname{Re}(w_r + \log x) \le -\log 2 < 0$ for $x \in (0, 1/2]$, both the non-identity $s$-channel correlator $\mathcal{G} - 1 = O(x^{h_{\mathrm{gap}}})$ and the $t$-channel identity $\operatorname{crossFactor}(\Delta_\phi, w_r + \log x) = O(x^{\Delta_\phi})$ are uniformly smooth in $w_r$ near $\operatorname{Re} w_r = 0$ with integrable $O(x^{\min(h_{\mathrm{gap}}, \Delta_\phi) - 1/2})$ bounds on $(0, 1/2]$. Thus the $(0, 1/2]$ integral extends smoothly across $\operatorname{Re} w_r = 0$ for $\theta \in [-\pi/2, \pi/2]$ with uniformly bounded $\theta$-derivatives of all orders!
     - **High-$x$ part $x \in [1/2, 1)$**:
       For $x \in [1/2, 1)$ and $\theta \in [-\pi/2, \pi/2]$, $\operatorname{Re}\bigl(\operatorname{crossW}(w_r + \log x)\bigr) \le -c \, |1 - x e^{w_r}|^2$.
       Using `exists_tChannel_twistGap_bound` (`RealLaplaceBound.lean`) and Cauchy's derivative formula (`norm_deriv_le_of_forall_mem_sphere_norm_le` in `CFT/Analysis/DominatedHolomorphy.lean`) on a disk of radius $\frac{1}{2}|1 - x e^{w_r}|$:
       $$\bigl\|\partial_{w_r}^j R(w_l, w_r + \log x)\bigr\| \le C_j \, |1 - x e^{w_r}|^{-2\Delta_\phi + 2 h_{\mathrm{gap}} - j}.$$
       Multiplying by $(1 - e^{w_r})^2 = O(u^2)$ in the $j = 2$ term of $\mathcal{D}_{\mathrm{inner}}$ (where $u = |1 - e^{w_r}| + (1 - x) \asymp |1 - x e^{w_r}|$) gives the uniform integrand bound (Equation (A.23)):
       $$\bigl\|K_{\mathrm{inner}}(w_r, x) \, \mathcal{D}_{\mathrm{inner}}(w_r, x, R(w_l, \cdot))\bigr\| \le C \, (1 - x)^{-1/2} \bigl(|1 - e^{w_r}| + 1 - x\bigr)^{-2\Delta_\phi + 2 h_{\mathrm{gap}} - 3/2},$$
       and after $N$ derivatives with respect to $\theta$ ($w_r = -\varepsilon + i\theta$), an extra factor $\bigl(|1 - e^{w_r}| + 1 - x\bigr)^{-N}$.

2. **Step 4.2 — Elementary Beta Tail Integral $I_N(e)$ (Appendix A.5, Equations (A.28)–(A.29))**:
   - Formalize the 1D real integral lemma `integral_rpow_sub_one_half_add_rpow_le`: for $e = |1 - e^{w_r}| > 0$ and $\beta = 2\Delta_\phi - 2 h_{\mathrm{gap}} + 1 + N$,
     $$\int_0^{1/2} y^{-1/2} (e + y)^{-1/2 - \beta} \, dy \le C_N \begin{cases} e^{-\beta}, & \beta > 0, \\ 1 + |\log e|, & \beta = 0, \\ 1, & \beta < 0. \end{cases}$$

3. **Step 4.3 — Localized Angular Integration by Parts on $[-\pi/2, \pi/2]$ (Lemma 3.1)**:
   - Formalize a smooth cutoff $\chi \in C_c^\infty\bigl((-\pi/2, \pi/2)\bigr)$ equal to $1$ on $[-\pi/4, \pi/4]$ (where $E_r(w_r)$ can be singular at $\theta = 0$) and $0$ near $\pm \pi/2$ (where $E_r$ is smooth and bounded).
   - For any target gap $h_{\mathrm{gap}} > 0$, choose an integer $N > \max(2 h_{\mathrm{gap}} - 2\Delta_\phi, 0)$ so that $\beta = 2\Delta_\phi - 2 h_{\mathrm{gap}} + 1 + N > 1$.
   - Integrating by parts $N$ times in $\theta$ on the $\chi$-localized integral (with zero boundary terms because $\chi$ vanishes near $\pm \pi/2$) and integrating by parts once on the complementary arc $[-\pi/2, -\pi/4] \cup [\pi/4, \pi/2]$ gives:
     $$\left\|(2k)^{-2\Delta_\phi} \int_{-\pi/2}^{\pi/2} e^{-2k(-\varepsilon + i\theta)} E_\sigma(-\varepsilon + i\theta) \, d\theta\right\| \le C \Bigl((2k)^{-2 h_{\mathrm{gap}}} + (2k)^{-2\Delta_\phi}\Bigr)$$
     for **all** $\Delta_\phi > 0$ and **all** $h_{\mathrm{gap}} > 0$ (including $h_{\mathrm{gap}} = \Delta_\phi$, removing even the $h_{\mathrm{gap}} \ne \Delta_\phi$ side condition!).

---

### Stage 5: Assembly in `TransmutedRealLaplace.lean` and `PrimaryLargeSpin.lean`

1. **Step 5.1 — Deriving `HasTransmutedCrossingGap` from `FourPointData` + `LightconeBlockFourPointData`**:
   - Combine Stages 2, 3, and 4 in `TransmutedRealLaplace.lean` to prove:
     ```lean
     theorem LightconeBlockFourPointData.hasTransmutedCrossingGap_of_correlator
         (corr : FourPointData ν Δ_phi) (hν : 0 ≤ ν) (hΔ : 0 < Δ_phi)
         (hL : L.AgreesWithCorrelator corr) :
         L.HasTransmutedCrossingGap Δ_phi
     ```
2. **Step 5.2 — Updating Theorem 2 in `PrimaryLargeSpin.lean` and `doc/monomial_bootstrap.tex`**:
   - State `exists_const_abs_muLC_sub_identity_le` and `exists_const_abs_primary_sub_identity_le` directly under `L.AgreesWithCorrelator corr` (Assumption 1 + Point 1 of Assumption 2 alone), completely removing Point 2 of Assumption 2 (`HasTransmutedCrossing`).
   - Update Section 3 of `doc/monomial_bootstrap.tex` so that Assumption 2 consists solely of the collinear block decomposition (Point 1).

---

## 5. Implementation Status & Summary Checklist

- [x] **Stage 1 (`TransmutedEndpointBounds.lean`, Sections 1 & 8)**: Defined `eulerD`, `transmuteInnerKernel`, `transmuteInnerDiff`, and `transmuteOpInner`; proved `transmuteOpInner_const` ($= 0$), `transmuteOpInner_block1d_of_pos`, `transmuteOpInner_block1d` for all $H \ge 0$, and `transmuteOpInner_block1d_eq_transmuteOp` for $H > 1/2$.
- [x] **Stage 2 (`TransmutedCrossing.lean`)**: Defined `gffBlockCoeff` and proved `gffBlockCoeff_mul_transmuteWeight_eq` and `hasSum_gffBlockCoeff_mul_transmuteOpInner_block1d`; defined `tChannelRemainder` and proved its holomorphy, low-$x$ ($x \in (0, 1/2]$) derivative bounds, high-$x$ ($x \in (1/2, 1)$) derivative bounds via `eval_eq_cross` + fixed-radius Cauchy ball on `crossW z`, and inner-transmutation integrability on `(0, 1)`; defined `LightconeBlockFourPointData.AgreesWithCorrelator` and proved `hasInnerTransmutedCrossing_of_agreesWithCorrelator`.
- [x] **Stage 3 (`ExactTransmutedRef.lean`, Sections 1–5)**: Defined `exactTransmutedPochhammer`, `exactTransmutedPolyFactor`, `crossFactorExactTransmuted`, `crossIdentityExactTransmuted`, `exactTransmutedIdentityLaplaceReal`, and `exactTransmutedIdentityPairing`; proved `exactTransmutedPochhammer_succ`, `exactTransmutedPochhammer_pos`, `hasSum_crossFactorExactTransmuted`, `exists_const_abs_exactTransmutedIdentityPairing_sub_universal_le` ($O(k^{-1})$ proximity to `transmutedUniversalPairing`), and `exists_const_abs_primary_sub_exactIdentity_le`.
- [x] **Stage 4 (`TransmutedEndpointBounds.lean`, Sections 2–7)**: Formalized the $x \in (0, 1/2] \cup (1/2, 1)$ split (`norm_transmuteOpInner_le_of_split_bounds`), the universal quadratic lower bound `le_norm_one_sub_mul_exp` and $(1 - e^{w_r})^2$ second-order cancellation (`norm_transmuteInnerKernel_mul_diff_le_of_source_bound`), the Beta tail bound $I_N(e)$ (`integral_rpow_neg_half_mul_add_rpow_le_of_le_two`), the low-$x$ / high-$x$ Cauchy derivative reductions (`norm_setIntegral_low_transmuteInner_le_of_re_le_bound`, `norm_transmuteInnerKernel_mul_diff_le_of_ball_bound`), and the folded $\theta$-contour bound (`norm_folded_integral_transmuteOpInner_le`).
- [x] **Stage 5 (`ExactTransmutedRef.lean`, `TransmutedCrossing.lean`, & `doc/monomial_bootstrap.tex`)**: Defined `LightconeBlockFourPointData.withGap` (automatically avoiding log resonances $2(h' - \Delta_\phi) \in \{0, 1\}$ for any $0 < \gamma < \min(2 h_{\mathrm{gap}}, 2\Delta_\phi)$), proved `exists_const_abs_muLC_sub_exactIdentity_le_of_agreesWithCorrelator` and `exists_const_abs_primary_sub_exactIdentity_le_of_agreesWithCorrelator` directly from `FourPointData` + `AgreesWithCorrelator`, and removed Point 2 of Assumption 2 in `doc/monomial_bootstrap.tex`.

