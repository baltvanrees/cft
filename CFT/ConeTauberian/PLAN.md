# Quantitative High-Energy Tauberian Asymptotics for $d$-Dimensional Primary Operators (Plan)

## 1. Goal & Mathematical Overview

This folder (`CFT/ConeTauberian/`) formalizes the **quantitative high-energy Tauberian asymptotics** for the primary operator product expansion (OPE) spectral measure at large scaling dimension $\Delta \to \infty$ in an arbitrary reflection-positive $d$-dimensional Conformal Field Theory ($d \ge 3$, $\nu = \frac{d-2}{2} > 0$).

Whereas `CFT/LightconeBootstrap/` analyzes the **large-spin lightcone limit** ($\ell \to \infty$ at fixed twist $\tau = \Delta - \ell$, controlled by $w_l \to -\infty, w_r \to 0^-$), this module analyzes the **bulk high-energy limit** ($\Delta \to \infty$ as a joint distribution in the rescaled scaling dimension $u = \Delta' / \Delta \in (0, \infty)$ and spin-to-dimension ratio $\xi = \ell / \Delta' \in (0, 1)$, controlled by $(w_l, w_r) \to (0, 0)$ in $\operatorname{UcPdisk}$).

### Setup & Statement of the Main Theorems

In `CFT/Blocks.lean`, `CFT/Corr.lean`, and `CFT/Corr_pdisk.lean`, the four-point correlation function of identical real scalar primary operators $\phi$ of scaling dimension $\Delta_\phi > 0$ is expanded on $\operatorname{UcPdisk}$ ($\rho_l = e^{w_l}, \rho_r = e^{w_r}$) against the non-negative OPE measure `corr.mu_measure` ($d\mu_{\text{OPE}}(\Delta', \ell)$ on $\mathbb{R} \times \mathbb{N}$):
$$\mathcal{G}_{\text{pdisk}}(w_l, w_r) = \int G_{\Delta', \ell}^{\text{pdisk}}(w_l, w_r) \, d\mu_{\text{OPE}}(\Delta', \ell),$$
where the conformal blocks `ConformalBlock ν Δ' l` are normalized in radial coordinates so that at leading order as $r \to 0$ (`(level 0).A l = 1`):
$$G_{\Delta', \ell}(r e^{i\theta}) \underset{r \to 0}{\sim} r^{\Delta'} \, C_\ell^{(\nu)}(\cos\theta).$$
By two-variable crossing symmetry (`crossing_correlator` in `CFT/Corr_pdisk.lean` and `norm_eval_sub_crossIdentity_le` in `CFT/LightconeBootstrap/Gap.lean`), as $(w_l, w_r) \to (0, 0)$ in $\operatorname{UcPdisk}$:
$$\mathcal{G}_{\text{pdisk}}(w_l, w_r) = \operatorname{crossIdentity}(\Delta_\phi, w_l, w_r) \Bigl(1 + O\bigl(\|w_l\|^{2 h_{\text{gap}}} + \|w_r\|^{2 h_{\text{gap}}}\bigr)\Bigr),$$
where $h_{\text{gap}} > 0$ is the $t$-channel twist gap and $\operatorname{crossIdentity}(\Delta_\phi, w_l, w_r) = \operatorname{crossFactor}(\Delta_\phi, w_l) \operatorname{crossFactor}(\Delta_\phi, w_r) \sim 4^{2\Delta_\phi} (-w_l)^{-2\Delta_\phi} (-w_r)^{-2\Delta_\phi}$.

Just as in `CFT/LightconeBootstrap/PrimaryLargeSpin.lean`, we separate the **genuinely non-universal dynamical error** (coming from non-identity $t$-channel operators above the twist gap $h_{\text{gap}} > 0$, which decays with exponent controlled **purely by $2 h_{\text{gap}}$**) from the **universal $O(\Delta^{-1})$ kinematic/Stirling expansion** of the $t$-channel identity and conformal blocks into their scale-invariant continuum limit:

$$\rho^{\text{prim}}_{\nu, \Delta_\phi}(u, \xi) := c_{\nu, \Delta_\phi} \, u^{4\Delta_\phi - 2\nu - 1} \, \xi^{2\nu} \left(1 - \xi^2\right)^{2\Delta_\phi - \nu - 3/2}, \qquad c_{\nu, \Delta_\phi} := \frac{2^{2\nu + 1} \, \Gamma(\nu) \, \Gamma(2\Delta_\phi - 1/2)}{\Gamma(\Delta_\phi)^4 \, \Gamma(2\Delta_\phi - \nu - 1/2)}.$$

We establish three main results:

1. **Theorem 1A — Quantitative Non-Universal Bound Against the Exact $t$-Channel Identity (Pure $2 h_{\text{gap}}$ Control, No $\Delta^{-1}$ Barrier)**:
   Under bilateral 1D transmutation $\mathcal{L}_0^{(w_l)} \otimes \mathcal{L}_0^{(w_r)}$, the exact $t$-channel identity $\operatorname{crossIdentity}(\Delta_\phi, w_l, w_r)$ defines a universal non-negative product measure $d\mu^{\text{id, trans}}_{2d}(\Delta_\phi; h', \bar{h}') = d\mu^{\text{id, trans}}_{1d}(\Delta_\phi; h') \otimes d\mu^{\text{id, trans}}_{1d}(\Delta_\phi; \bar{h}')$ on $(0, \infty)^2$. For **all** $\Delta_\phi > 0$, **all** $h_{\text{gap}} > 0$, and any compactly supported test function $\psi \in C_c^2((0, \infty)^2)$, there exist $\gamma > 0$ controlled **purely by $2 h_{\text{gap}}$** (with no `1` and no $2\Delta_\phi$ restriction) and $C_\psi > 0$ such that for all $\Delta \ge 1$:
   $$\boxed{\left|\Delta^{-2 - 4\Delta_\phi} \int \psi\!\left(\frac{h'}{\Delta},\, \frac{\bar{h}'}{\Delta}\right) d\mu^{\text{trans}}_{2d}(h', \bar{h}') - \Delta^{-2 - 4\Delta_\phi} \int \psi\!\left(\frac{h'}{\Delta},\, \frac{\bar{h}'}{\Delta}\right) d\mu^{\text{id, trans}}_{2d}(\Delta_\phi; h', \bar{h}')\right| \le C_\psi \, \Delta^{-\gamma},}$$
   where $\int \psi(h'/\Delta, \bar{h}'/\Delta) \, d\mu^{\text{trans}}_{2d}(h', \bar{h}') = \int (\mathcal{B}_{\nu, \Delta} \psi)(\Delta', \ell) \, d\mu_{\text{OPE}}(\Delta', \ell)$ is the exact $d \to 2$ branched primary OPE functional.

2. **Theorem 1B — Quantitative $O(\Delta^{-\gamma})$ Smoothed Primary Bootstrap Against the Continuum Density $\rho^{\text{prim}}_{\nu, \Delta_\phi}(u, \xi)$**:
   Combining Theorem 1A with the uniform $O(\Delta^{-1})$ Stirling expansion of the universal $t$-channel identity measure $d\mu^{\text{id, trans}}_{2d}(\Delta_\phi)$ and the discrete $d \to 2$ branching operator $\mathcal{B}_{\nu, \Delta}$, for any $\nu > 0$, $\Delta_\phi > \frac{\nu}{2} + \frac{1}{4}$, $h_{\text{gap}} > 0$, and any smooth test function $\chi : \mathbb{R} \times \mathbb{R} \to \mathbb{R}$ compactly supported in $(0, \infty) \times (0, 1)$ (whose inverse Erdélyi–Kober transform in $\xi$ is $C_c^2$ on $(0, \infty) \times (0, 1)$), there exist $\gamma > 0$ (controlled by $\min(2 h_{\text{gap}},\, 1)$) and $C_\chi > 0$ such that for all $\Delta \ge 1$:
   $$\boxed{\left|\Delta^{2\nu - 4\Delta_\phi} \int \chi\!\left(\frac{\Delta'}{\Delta},\, \frac{\ell}{\Delta'}\right) d\mu_{\text{OPE}}(\Delta', \ell) - \int_0^\infty \int_0^1 \chi(u, \xi) \, \rho^{\text{prim}}_{\nu, \Delta_\phi}(u, \xi) \, d\xi \, du\right| \le C_\chi \, \Delta^{-\gamma}.}$$

3. **Corollary 2 — Cumulative Spin-Summed Primary Asymptotics**:
   For $\Delta_\phi > \frac{\nu}{2} + \frac{1}{4}$, the exponents $4\Delta_\phi - 2\nu - 1 > -1$, $2\nu > -1$, and $2\Delta_\phi - \nu - 3/2 > -1$ ensure that $\rho^{\text{prim}}_{\nu, \Delta_\phi}(u, \xi)$ is integrable on the full cylinder $(u, \xi) \in (0, 1] \times [0, 1]$, with total integral
   $$\mathcal{C}^{\text{prim}}_\nu(\Delta_\phi) := \int_0^1 \int_0^1 \rho^{\text{prim}}_{\nu, \Delta_\phi}(u, \xi) \, d\xi \, du = \frac{2^{2\nu - 1} \, \Gamma(\nu) \, \Gamma(\nu + 1/2) \, \Gamma(2\Delta_\phi - 1/2)}{\left(2\Delta_\phi - \nu\right) \Gamma(\Delta_\phi)^4 \, \Gamma(2\Delta_\phi)},$$
   and the cumulative unweighted primary OPE spectral weight up to scaling dimension $\Delta$ satisfies
   $$\int_{\Delta' \le \Delta} d\mu_{\text{OPE}}(\Delta', \ell) \;\underset{\Delta \to \infty}{\sim}\; \mathcal{C}^{\text{prim}}_\nu(\Delta_\phi) \, \Delta^{4\Delta_\phi - 2\nu}.$$

---

## 2. Mathematical Strategy

1. **Bilateral 1D Transmutation ($\mathcal{L}_0^{(w_l)} \otimes \mathcal{L}_0^{(w_r)}$) on 2D Conformal Blocks**:
   - A 2D conformal block is a symmetrized product of 1D $SL(2, \mathbb{R})$ blocks $\operatorname{block1d}(h', w_l) \operatorname{block1d}(\bar{h}', w_r)$ (`CFT/Blocks_1d.lean`), where $h' = \frac{\Delta' - j}{2}$ and $\bar{h}' = \frac{\Delta' + j}{2}$.
   - In `CFT/LightconeBootstrap/Transmute1d.lean`, the 1D fractional transmutation operator `transmuteOp` ($\mathcal{L}_0$) acts on $w \in \operatorname{UcDisk}$ independently of $H$ and maps every 1D block identically to a single exponential (`transmuteOp_block1d`):
     $$\mathcal{L}_0\bigl[\operatorname{block1d}(H, \cdot)\bigr](w) = \operatorname{transmuteWeight}(H) \, e^{H w}, \qquad \operatorname{transmuteWeight}(H) = \left(H - \frac{1}{2}\right)\frac{\Gamma(H + 1/2)}{\Gamma(H)}.$$
   - Applying $\mathcal{L}_0$ in both variables $(w_l, w_r) \in \operatorname{UcPdisk}$ reduces every 2D block identically to the two-variable exponential
     $$\operatorname{transmuteWeight}(h') \operatorname{transmuteWeight}(\bar{h}') \, e^{h' w_l + \bar{h}' w_r}.$$

2. **Quantitative $O(\Delta^{-\gamma})$ 2D Tauberian Theorem via Rescaled Fejér Kernel (`Karamata2d.lean`)**:
   - Under the rescaling $(u_l, u_r) = (h'/\Delta, \bar{h}'/\Delta) \in (0, \infty)^2$, evaluating the bilaterally transmuted correlator at complex points
     $$w_l = \frac{-A + i t_l}{\Delta}, \qquad w_r = \frac{-A + i t_r}{\Delta} \qquad (A > 0)$$
     yields the exact 2D Fourier transform at frequency $(t_l, t_r) \in \mathbb{R}^2$ of the exponentially tilted rescaled measure $e^{-A(u_l + u_r)} d\mu^{\text{trans}}_\Delta(u_l, u_r)$.
   - For all frequencies $|t_l|, |t_r| \le 2\pi T$ ($T = \Delta^\delta$), $w_i = (-A + i t_i)/\Delta \to 0$ as $\Delta \to \infty$ (with $|\operatorname{Im}(w_i)| \le 2\pi \Delta^{\delta - 1} \to 0$, so there is **no outer contour**). Thus $(w_l, w_r)$ lies directly inside the $t$-channel OPE convergence neighborhood (`Gap.lean`), where the difference between the CFT's transmuted Fourier-Laplace transform and the exact transmuted $t$-channel identity transform is bounded purely by the non-identity $t$-channel remainder $O\bigl((1 + T)^p \Delta^{-2 h_{\text{gap}}}\bigr)$.
   - Convolving any compactly supported $C_c^2$ test function $\psi(u_l, u_r)$ with the 2D rescaled Fejér kernel $K_T(u_l) K_T(u_r) = T^2 K(T u_l) K(T u_r)$ (`fejerKernel_eq_fourier_integral` in `CFT/Analysis/HermiteMeasure.lean`) restricts the Fourier integral to $[-2\pi T, 2\pi T]^2$, while the Fejér convolution remainder $|\psi - \psi * (K_T \otimes K_T)|$ decays as a power of $T^{-1}$. Optimizing $T = \Delta^\delta$ yields **Theorem 1A** with an explicit $O(\Delta^{-\gamma})$ error bound controlled **purely by $2 h_{\text{gap}}$** for every $\psi \in C_c^2((0, \infty)^2)$.

3. **Universal $O(\Delta^{-1})$ Stirling & Erdélyi–Kober Reduction to Continuum Density (`Branching2d.lean`, `ErdelyiKoberInversion.lean`)**:
   - Replacing the exact universal $t$-channel identity measure $d\mu^{\text{id, trans}}_{2d}(\Delta_\phi)$ and the discrete $d \to 2$ branching coefficients (`geg_two_var_sum` in `CFT/Gegenbauers.lean`) by their continuum Stirling limits (`exists_abs_rpow_mul_pochhammerCoeff_sub_inv_gamma_le` in `CFT/LightconeBootstrap/RealLaplaceBound.lean`) incurs a universal $O(\Delta^{-1})$ error on compact subsets of $(u, \xi) \in (0, \infty) \times (0, 1)$ and converges to the Erdélyi–Kober fractional integral with kernel
     $$\mathcal{K}_\nu(\xi, \xi') := \frac{2^{2 - 2\nu}}{\Gamma(\nu)^2} \, \xi^{1 - 2\nu} \left(\xi^2 - (\xi')^2\right)^{\nu - 1} \mathbf{1}_{\xi' < \xi}.$$
   - By the Euler Beta integral identity, the adjoint Erdélyi–Kober operator maps $\rho^{\text{prim}}_{\nu, \Delta_\phi}(u, \xi)$ onto the 2D effective density $\rho_{2d}^{\text{eff}}(u, \xi')$, combining with Theorem 1A to yield **Theorem 1B** with error exponent controlled by $\min(2 h_{\text{gap}},\, 1)$.

---

## 3. Dictionary of Notation

| Mathematical Object | Lean Name / File | Definition / Formula |
|---|---|---|
| Spacetime dimension parameter | `ν` (`Blocks.lean`, `Corr.lean`) | $\nu = \frac{d - 2}{2} > 0$ ($d = 2\nu + 2 \ge 3$) |
| 1D collinear block | `block1d H w` (`Blocks_1d.lean`) | $\sum_{n=0}^\infty \frac{(H)_n (1/2)_n}{(H + 1/2)_n \, n!} e^{(H + 2n) w}$ |
| 1D transmutation operator & weight | `transmuteCore`, `transmuteOp`, `transmuteWeight` (`Transmute1d.lean`) | $\mathcal{L}_0[\operatorname{block1d} H](w) = \operatorname{transmuteWeight}(H) e^{H w}$ |
| 2D conformal block | `block2d Δ j wl wr` *(new, `Branching2d.lean`)* | $\frac{1}{1 + \delta_{j, 0}} \bigl[\operatorname{block1d}(\frac{\Delta - j}{2}, w_l)\operatorname{block1d}(\frac{\Delta + j}{2}, w_r) + (w_l \leftrightarrow w_r)\bigr]$ |
| Exact 2D transmuted $t$-channel identity measure | `transmutedIdentityMeasure2d Δ_phi` *(new, `ConeAsymptotics.lean`)* | $d\mu^{\text{id, trans}}_{1d}(\Delta_\phi) \otimes d\mu^{\text{id, trans}}_{1d}(\Delta_\phi)$ |
| Gegenbauer angular coefficients | `geg_two_var_sum`, `pochhammerCoeff` (`Gegenbauers.lean`, `RealLaplaceBound.lean`) | $\frac{(\nu)_m (\nu)_{\ell - m}}{m! (\ell - m)!}$ for $j = \ell - 2m$ |
| Gegenbauer-to-2D spin coefficients | `branchingSpinCoeff ν l m` ($b_m^{(\nu)}(\ell)$) *(new, `Branching2d.lean`)* | $(2 - \delta_{\ell - 2m, 0}) \frac{(\nu)_m (\nu)_{\ell - m}}{m! (\ell - m)!}$ |
| Transverse shift coefficients | `branchingShiftCoeff ν Δ l k` ($a_k^{(\nu)}(\Delta, \ell)$) *(new, `Branching2d.lean`)* | $\frac{(\nu - 1/2)_k}{k!} + O(1/\Delta)$ |
| Continuum branching kernel | `branchingKernel ν ξ ξ'` ($\mathcal{K}_{\nu}$) *(new, `Branching2d.lean`)* | $\frac{2^{2 - 2\nu}}{\Gamma(\nu)^2} \xi^{1 - 2\nu} (\xi^2 - (\xi')^2)^{\nu - 1} \mathbf{1}_{\xi' < \xi}$ |
| 2D effective density | `eff2dDensity Δ_phi u ξ'` *(new, `ErdelyiKoberInversion.lean`)* | $\frac{4}{\Gamma(\Delta_\phi)^4} u^{4\Delta_\phi - 2} \bigl(1 - (\xi')^2\bigr)^{2\Delta_\phi - 3/2}$ |
| Erdélyi–Kober fractional integral | `weylIntegralRight ν g`, `weylIntegralLeft ν φ` *(new, `ErdelyiKoberInversion.lean`)* | $\frac{1}{\Gamma(\nu)} \int_{s'}^1 (s - s')^{\nu - 1} g(s) \, ds$ ($s = \xi^2$) |
| Primary spectral density constant | `primaryConeConst ν Δ_phi` ($c_{\nu, \Delta_\phi}$) *(new, `ErdelyiKoberInversion.lean`)* | $\frac{2^{2\nu + 1} \Gamma(\nu) \Gamma(2\Delta_\phi - 1/2)}{\Gamma(\Delta_\phi)^4 \Gamma(2\Delta_\phi - \nu - 1/2)}$ |
| Continuum primary spectral density | `primaryConeDensity ν Δ_phi u ξ` ($\rho^{\text{prim}}_{\nu, \Delta_\phi}(u, \xi)$) *(new, `ErdelyiKoberInversion.lean`)* | $c_{\nu, \Delta_\phi} \, u^{4\Delta_\phi - 2\nu - 1} \xi^{2\nu} (1 - \xi^2)^{2\Delta_\phi - \nu - 3/2}$ |
| Cumulative primary constant | `cumulativePrimaryConst ν Δ_phi` ($\mathcal{C}^{\text{prim}}_\nu(\Delta_\phi)$) *(new, `ErdelyiKoberInversion.lean`)* | $\frac{2^{2\nu - 1} \Gamma(\nu) \Gamma(\nu + 1/2) \Gamma(2\Delta_\phi - 1/2)}{(2\Delta_\phi - \nu) \Gamma(\Delta_\phi)^4 \Gamma(2\Delta_\phi)}$ |

---

## 4. Proposed File Structure

We add one standalone 2D quantitative Tauberian analysis file in `CFT/Analysis/` and three CFT files in `CFT/ConeTauberian/`:

```text
CFT/Analysis/
  └── Karamata2d.lean                 (Stage 3: Quantitative O(Δ^{-γ}) two-variable Fourier-Laplace
                                       Tauberian theorem for compactly supported C_c^2 functions
                                       on (0, ∞)² via rescaled Fejér convolution K_T(u_l) K_T(u_r))

CFT/ConeTauberian/
  ├── PLAN.md                         (This file: mathematical plan & checklist)
  ├── ErdelyiKoberInversion.lean      (Stage 1: Continuum primary density ρ^{prim}_{ν, Δ_φ}(u, ξ),
  │                                    Weyl/Erdélyi–Kober fractional integrals I_±^ν on (0, 1),
  │                                    Euler Beta eigenfunction identity, and Fubini duality)
  ├── Branching2d.lean                (Stage 2: 2D blocks, bilateral transmutation L_0 ⊗ L_0,
  │                                    d → 2 branching coefficients b_m^{(ν)}(l), and uniform
  │                                    O(1/Δ) Stirling convergence to the Erdélyi–Kober kernel K_ν)
  └── ConeAsymptotics.lean            (Stage 4: ConeBlockFourPointData, Theorem 1A (pure 2 h_gap
                                       bound against exact t-channel identity), Theorem 1B (min(2 h_gap, 1)
                                       bound against continuum density ρ^{prim}_{ν, Δ_φ}), and
                                       Corollary 2 (cumulative spin-summed primary asymptotics))
```

---

## 5. Step-by-Step Implementation Checklist

### Phase 1: Erdélyi–Kober Fractional Integral & Primary Spectral Density (`ErdelyiKoberInversion.lean`)
- [x] **Step 1.1 (`primaryConeConst`, `primaryConeDensity`, `cumulativePrimaryConst`, and Cylinder Integrability)**:
  - Define `primaryConeConst ν Δ_phi` ($c_{\nu, \Delta_\phi}$), `primaryConeDensity ν Δ_phi u ξ` ($\rho^{\text{prim}}_{\nu, \Delta_\phi}(u, \xi)$), `eff2dDensity Δ_phi u ξ'` ($\rho_{2d}^{\text{eff}}(u, \xi')$), and `cumulativePrimaryConst ν Δ_phi` ($\mathcal{C}^{\text{prim}}_\nu(\Delta_\phi)$).
  - Prove non-negativity and the exact Beta integral evaluation
    $$\int_0^1 \int_0^1 \rho^{\text{prim}}_{\nu, \Delta_\phi}(u, \xi) \, d\xi \, du = \mathcal{C}^{\text{prim}}_\nu(\Delta_\phi)$$
    (`integral_primaryConeDensity_cylinder`) for $\Delta_\phi > \frac{\nu}{2} + \frac{1}{4}$ and $\nu > 0$ via the substitution $s = \xi^2$ (`integral_Ioo_sq_sub`) and `integral_rpow_mul_one_sub_rpow`.
- [x] **Step 1.2 (Weyl / Erdélyi–Kober Fractional Integral & Exact Power-Law Eigenfunction Identity)**:
  - Define the right-handed and left-handed Erdélyi–Kober fractional integrals `weylIntegralRight ν g s'` and `weylIntegralLeft ν φ s` on $(0, 1)$.
  - Prove the fundamental Beta identity (`weylIntegralRight_one_sub_rpow`):
    $$\frac{1}{\Gamma(\nu)} \int_{s'}^1 (s - s')^{\nu - 1} (1 - s)^{\alpha - 1} \, ds = \frac{\Gamma(\alpha)}{\Gamma(\alpha + \nu)} (1 - s')^{\alpha + \nu - 1} \qquad (\nu > 0,\; \alpha > 0,\; s' < 1),$$
    and deduce (`integral_branching_mul_primaryConeDensity`) that the continuum $d \to 2$ branching kernel $u^{2\nu - 1} \mathcal{K}_\nu(\xi, \xi')$ maps the primary spectral density $\rho^{\text{prim}}_{\nu, \Delta_\phi}(u, \xi)$ onto the 2D effective density $\rho_{2d}^{\text{eff}}(\Delta_\phi, u, \xi')$.
- [x] **Step 1.3 (Monotone Sandwiching Lemma for Cumulative Asymptotics)**:
  - Prove the monotone sandwiching lemma (`tendsto_of_le_of_ge_approx`) for deducing cumulative asymptotics from smooth test function approximations.

### Phase 2: $d \to 2$ Conformal Block Branching & Quantitative $O(\Delta^{-1})$ Stirling Bound (`Branching2d.lean`)
- [x] **Step 2.1 (`block2d` and Bilateral Transmutation $\mathcal{L}_0 \otimes \mathcal{L}_0$)**:
  - Define `block2dChiral hl hr wl wr` and `block2d Δ j wl wr` from `block1d` (`CFT/Blocks_1d.lean`), and the bilateral transmutation operator `transmuteOp2d`.
  - Prove (`transmuteOp2d_block2dChiral`, `transmuteOp2d_block2d`) that applying `transmuteOp` (`CFT/LightconeBootstrap/Transmute1d.lean`) in both $w_l$ and $w_r$ maps `block2d Δ' j wl wr` to a symmetrized pure exponential with weight $\operatorname{transmuteWeight}(\frac{\Delta' - j}{2}) \operatorname{transmuteWeight}(\frac{\Delta' + j}{2})$.
- [x] **Step 2.2 (Gegenbauer-to-2D Spin Coefficients $b_m^{(\nu)}(\ell)$ & Transverse Shift Resummation)**:
  - Define `gegSpinCoeff ν l m` and `branchingSpinCoeff ν l m` using `pochhammerCoeff` (`RealLaplaceBound.lean`), connect them to `gegenbauer` via `gegenbauer_eval_Trigger_eq_sum_gegSpinCoeff` (`CFT/Gegenbauers.lean`), and prove non-negativity for $\nu \ge 0$.
  - Prove the transverse shift binomial identity (`hasSum_transverseShift`, `tsum_transverseShift`) $\sum_{k=0}^\infty \operatorname{pochhammerCoeff}(\nu - 1/2, k) (1 - \xi^2)^k = \xi^{1 - 2\nu}$ for $\xi \in (0, 1)$ using `hasSum_one_sub_rpow_neg`.
- [x] **Step 2.3 (Uniform $O(\Delta^{-1})$ Stirling Convergence of `gegSpinCoeff` and `transmuteWeight`)**:
  - Using `exists_abs_rpow_mul_pochhammerCoeff_sub_inv_gamma_le` (`RealLaplaceBound.lean`), prove the explicit $O(m^{-1} + (\ell - m)^{-1})$ product Stirling bound `exists_abs_rpow_mul_gegSpinCoeff_sub_inv_gamma_sq_le` and the $O(n^{-1})$ Stirling bound `exists_abs_rpow_mul_transmuteWeight_nat_sub_one_le`.

### Phase 3: Quantitative Two-Variable Fourier-Laplace Tauberian Theorem (`CFT/Analysis/Karamata2d.lean`)
- [x] **Step 3.1 (Bandlimited Fourier Truncation on $[-R, R]^2$ & $O(R^{-1})$ Tail Decay)**:
  - Define `laplaceTransform2d`, `laplaceTransformReal2d`, `tiltedMeasure2d`, `tiltedTest2d`, `HasFourierDecay2d`, `freqBox R`, and `bandlimitedApprox2d`, and prove the uniform $L^\infty$ tail bound `norm_sub_bandlimitedApprox2d_le` and Fubini pairing identity `integral_bandlimitedApprox2d_tiltedMeasure2d`.
- [x] **Step 3.2 (Non-Asymptotic & Quantitative $O(\Delta^{-\gamma})$ 2D Tauberian Bounds)**:
  - Prove the non-asymptotic 2D Tauberian bound `abs_integral_sub_le_of_laplace2d_bound` and the quantitative $O(\Delta^{-\gamma})$ power-law 2D Tauberian theorem `exists_const_abs_integral_sub_le_rpow_2d` with optimal frequency cutoff $R = \Delta^\gamma$, $\gamma = \alpha / (p_{\text{deg}} + 1) > 0$.

### Phase 4: Main Quantitative & Cumulative Primary Theorems (`ConeAsymptotics.lean`)
- [x] **Step 4.1 (`ConeBlockFourPointData` & Bilateral Transmuted Crossing Bound)**:
  - Package the $d$-dimensional primary measure `μ_OPE`, rescaled 2D transmuted measure `μ_trans2d Δ`, exact rescaled 2D transmuted $t$-channel identity measure `μ_id2d Δ`, and pure $O(\Delta^{-2 h_{\text{gap}}})$ bilateral transmuted crossing bound into `ConeBlockFourPointData` and `HasBilateralCrossingGap`.
- [x] **Step 4.2 (Theorem 1A & Theorem 1B — Quantitative Non-Universal ($2 h_{\text{gap}}$) & Continuum ($\min(2 h_{\text{gap}}, 1)$) Primary Bootstrap)**:
  - Apply `Karamata2d.lean` directly to prove **Theorem 1A** (`exists_const_abs_transmuted2d_sub_identity_le`, `tendsto_transmuted2d_sub_identity`) with exponent controlled **purely by $2 h_{\text{gap}}$** for all $\Delta_\phi > 0$ and $h_{\text{gap}} > 0$.
  - Combine Theorem 1A with `HasUniversalBranchingReduction` and `ErdelyiKoberInversion.lean` (`integral_branchingKernel_mul_primaryConeDensity`) to prove **Theorem 1B** (`exists_const_abs_primaryCone_sub_le`, `tendsto_primaryConePairing`) with exponent controlled by $\min\bigl(\frac{2 h_{\text{gap}}}{p_{\text{deg}} + 1},\, 1\bigr)$.
- [x] **Step 4.3 (Corollary 2 — Cumulative Spin-Summed Primary Asymptotics)**:
  - Prove `continuumPrimaryPairing_unitCylinderIndicator` and apply `tendsto_of_le_of_ge_approx` to deduce the unweighted cumulative primary asymptotic (`tendsto_cumulativePrimaryWeight`) for $\Delta_\phi > \frac{\nu}{2} + \frac{1}{4}$.
