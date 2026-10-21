# An explicit neighborhood preserving four simple blind gains

For the fixed 63-site pair, independent centered Gaussian site phases with
attenuation $t=e^{-s/2}$, and conditional counts
$N\mid I\sim\operatorname{Poisson}(b+\eta I)$ with common background,
the difference $\Pr_A(N=4)-\Pr_B(N=4)$ has **exactly four simple positive
zeros in gain** throughout the closed parameter rectangle

$$|t-1/2|\le10^{-23},\qquad 0\le b\le10^{-20}.$$

This is an analytic result supported by an [exact rational budget checker](../tools/check_root_stability.py)
and its [executed receipt](validation/root_stability.json). It depends on the
retained reference enclosures and moment identities. It supplies a radius
missing from the [earlier existence proof](../evidence/followup-2026-10-20/stability/local_stability_proof.txt).
It is **not Lean-formalized**. These deliberately conservative radii are much
too small to establish an experimentally useful tolerance; they are not
claimed optimal. This result concerns the four-count indicator, not blindness
of the full count law, which remains distinct at every positive gain.

## 1. Inputs and normalized functions

Write $\Delta E_t=E_{A,t}-E_{B,t}$ and $M=3969$, so $0\le I\le M$.
The [concrete moment proof](../formal/CERTIFICATES.md) gives
$\Delta E_t I^k=0$ for $k=0,1,2,3$ and

$$D_4(t)=\frac{455015761}{20000}t^8(1-t^2)^5(t^6+3t^4+6t^2+6)>0.$$

Set $q_b(z)=e^{-z}(b+z)^4$ and
$Z(t,b,\eta)=\Delta E_t q_b(\eta I)=24e^b\Delta\Pr(N=4)$.
For $\eta>0$ define $H=Z/\eta^4$. For $y>0$ define
$G(t,b,y)=Z(t,b,1/y)/(24y)$. At $(t,b)=(1/2,0)$ these are precisely
the archived functions $F(\eta)$ and $F(1/y)/(24y^5)$.
The positive normalizing factors preserve roots and their multiplicities
at finite positive gain.

All parameter estimates below hold on the larger rectangle
$2/5\le t\le3/5$, $0\le b\le1/8$.
The retained [uniform Fourier derivation](../evidence/followup-2026-10-20/stability/local_stability_proof.txt),
sections 1–2, proves the single-site phase-density derivative bound
$\|\partial_t w_t\|_1<8$ and the characteristic bound
$|\phi_t(r,\theta)|\le\min(1,7/\sqrt r)$.
The checker recomputes the rational constants establishing both inequalities.
For the product of 63 site laws, differentiation therefore costs at most
$63\cdot8=504$ in $L^1$ per structure. For the difference of two expectations
of a bounded, parameter-independent function, the cost is at most 1008 times
its supremum norm. This bound uses phase coordinates, where intensity itself
does not depend on $t$.

## 2. Uniform control at finite gain, including zero

Taylor's integral remainder and the four matching moments give the exact identity

$$H(t,b,\eta)=\frac16\Delta E_t\left[I^4\int_0^1(1-u)^3q_b^{(4)}(u\eta I)\,du\right].$$

This defines a smooth extension to $\eta=0$, with
$H(t,b,0)=D_4(t)L_4(b)$, where
$L_4(b)=1-4b+3b^2-2b^3/3+b^4/24$.
Differentiating gives

$$H_\eta(t,b,\eta)=\frac16\Delta E_t\left[I^5\int_0^1u(1-u)^3q_b^{(5)}(u\eta I)\,du\right].$$

For $z\ge0$ and $0\le b\le1/8$,

$$e^{-z}(b+z)^m\le m!\sum_{j=0}^m\frac{b^j}{j!}\le\frac87m!.$$

The first inequality follows by expanding the power and using
$e^{-z}z^k\le k!$. Leibniz's rule consequently gives the uniform bounds

| Derivative | Bound |
| --- | ---: |
| $\lvert q_b^{(4)}\rvert$ | $3072/7$ |
| $\lvert q_b^{(5)}\rvert$ | $5952/7$ |
| $\lvert\partial_bq_b^{(4)}\rvert$ | $2880/7$ |
| $\lvert\partial_bq_b^{(5)}\rvert$ | $4992/7$ |

For example the first two bounds are $(8/7)4!\sum_{j=0}^4\binom{k}{j}$
with $k=4,5$. A background derivative replaces the upper summation index
by 3. The integrated Taylor weights are $1/24$ for $H$ and $1/120$ for
$H_\eta$. It follows that

| Function $X$ | $\lvert\partial_t X\rvert\le L_{X,t}$ | $\lvert\partial_b X\rvert\le L_{X,b}$ |
| --- | --- | --- |
| $H$ | $42M^4(3072/7)$ | $M^4(2880/7)/12$ |
| $H_\eta$ | $(42/5)M^5(5952/7)$ | $M^5(4992/7)/60$ |

These estimates hold for every $\eta\ge0$, not just near zero.
The factors 1008 for the phase derivative and 2 for the background
derivative include both structures. Bounded intensity and the displayed
uniform bounds justify differentiating the integrals.

## 3. Uniform control at infinite gain through inverse gain

Let $\Delta\psi_t(r)$ be the difference of the angularly averaged planar
characteristic functions. The same product bounds give

$$|\Delta\psi_t(r)|\le2B_{63}(r),\qquad
|\partial_t\Delta\psi_t(r)|\le1008B_{62}(r),\qquad
B_m(r)=\min(1,7^m r^{-m/2}).$$

Fourier inversion gives the intensity-density difference
$\Delta h_t(v)=\tfrac12\int_0^\infty r\Delta\psi_t(r)J_0(r\sqrt v)\,dr$.
Changing variables in $Z$ and integrating the Bessel kernel yields

$$G(t,b,y)=\frac12\int_0^\infty r\Delta\psi_t(r)W_b(r^2y/4)\,dr,$$

$$W_b(x)=\sum_{j=0}^4\frac{b^j}{j!}K_{4-j}(x),\qquad
K_k(x)=e^{-x}L_k(x),\qquad
L_k(x)=\sum_{\ell=0}^k\binom{k}{\ell}\frac{(-x)^\ell}{\ell!}.$$

To check the normalization, use
$\int_0^\infty v^k e^{-v}J_0(2\sqrt{xv})\,dv=k!e^{-x}L_k(x)$.
This identity follows by differentiating $k$ times in $a$ the transform
$\int_0^\infty e^{-av}J_0(2\sqrt{xv})\,dv=a^{-1}e^{-x/a}$, then setting
$a=1$. Expanding $(b+v)^4/24$ gives exactly the coefficients $b^j/j!$.
Absolute integrability of $rB_{63}(r)$ and the exponential weight justifies
the exchange of integrals.

For $x\ge0$, the finite Laguerre sums give
$|K_k(x)|\le2^k$ and $|K'_k(x)|\le2^{k+1}-1$.
Since $e^{b/2}\le(1-b/2)^{-1}\le16/15$, the following slightly enlarged
bounds hold uniformly:

$$|W_b|\le256/15,\quad |\partial_xW_b|\le512/15,\quad
|\partial_bW_b|\le128/15,\quad |\partial_b\partial_xW_b|\le256/15.$$

Splitting the integral at $r=49$ gives, when $m>2p+2$,

$$J_{p,m}=\int_0^\infty r^pB_m(r)\,dr
=7^{2p+2}\left(\frac1{p+1}+\frac2{m-2p-2}\right).$$

Differentiation under the integrals is justified by these integrable
envelopes, including at $y=0$ from the right. In particular $G$ and $G_y$
extend continuously there, and

| Function $X$ | $L_{X,t}$ | $L_{X,b}$ |
| --- | --- | --- |
| $G$ | $504(256/15)J_{1,62}$ | $(128/15)J_{1,63}$ |
| $G_y$ | $126(512/15)J_{3,62}$ | $(64/15)J_{3,63}$ |

The $y$ derivative introduces $r^2/4$. In particular the factor for
$\partial_bG_y$ is $(1/8)\cdot2\cdot(256/15)=64/15$.
The bounds hold on the entire inverse-gain interval $[0,6]$; its endpoint
$y=0$ controls arbitrarily large gains.

## 4. Exact margins and root count

For each of $X=H,H_\eta,G,G_y$, the mean-value bound along a path inside
the larger parameter rectangle gives

$$|X(t,b,\cdot)-X(1/2,0,\cdot)|
\le E_X:=10^{-23}L_{X,t}+10^{-20}L_{X,b}.$$

The checker reads five SHA256-pinned reference certificates, validates
their complete closed covers and strict signs, and checks $2E_X\le m_X$
against **every required group's smallest exact rational margin**.
It uses the signed rational enclosures, never their decimal display strings.
The first certificate's Bernstein upper bounds directly bound $F$ and $F'$;
no hidden polynomial scale factor is discarded.
Thus each retained sign has at least half its original certified margin.
For scale only, the smallest required $H$ margin exceeds $0.000679$, while
$E_H<0.000131$. The receipt contains the exact inequalities.

The preserved signs and derivative signs cover all gains as follows:

| Gain interval | Preserved property |
| --- | --- |
| $[0,1/512]$ | $H_\eta<0$, with $H(0)>0$ and $H(1/512)<0$ |
| $[1/512,1/100]$ | $H<0$ |
| $[1/100,1/90]$ | $H_\eta>0$, with opposite endpoint signs |
| $[1/90,1/23]$ | $H>0$ |
| $[1/23,1/22]$ | $H_\eta<0$, with opposite endpoint signs |
| $[1/22,1/6]$ | $H<0$ |
| $\eta\ge1/6$, equivalently $0<y\le6$ | $G_y<0$ on $[0,6]$, $G(0)>0$, $G(6)<0$ |

The intermediate value theorem and strict monotonicity give one simple
root in each of $(0,1/512)$, $(1/100,1/90)$, $(1/23,1/22)$, and
$(1/6,\infty)$. The signed intervening intervals exclude any additional
root. The fourth root is simple in gain because $dy/d\eta=-1/\eta^2$
is nonzero at a finite positive root. This proves the stated count for
the whole rectangle, including its boundary.

## Reproduction and limits

```console
python tools/check_root_stability.py --output build/root-stability.json
python -m unittest discover -s tests
```

The checker recomputes the perturbation arithmetic; it does not regenerate
the inherited reference enclosures or mechanically verify this analytic
derivation. The [extended arithmetic replay](reproduction.md) checks the
retained calculations, with its documented coverage. Formalizing the root
proof, finding useful larger radii, classifying the whole parameter domain,
experimental validation, and novelty assessment remain separate work.
This rectangle also differs from the [fixed-score model-error budget](model-tolerance.md),
which concerns testing error rather than the number of blind gains.
