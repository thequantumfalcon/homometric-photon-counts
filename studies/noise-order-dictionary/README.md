# Which noisy-intensity moment first separates a homometric pair?

This is a separately labelled **numerical study**. It uses 40-digit floating
point, not interval arithmetic or a proof assistant, and it changes none of
the repository's theorems, certificates or evidence inventory. No
measurement, novelty or priority is claimed.

## Question

Under the primary model (one frequency, iid centered Gaussian site phases with
`t = exp(-s/2)`, so `E exp(i m theta) = t^(m^2)`), every intensity moment
`E[I^k]` is a polynomial in charge-neutral monomials of the harmonic sums
`M_m = sum_j z_j^m`:

```text
T = prod M_(a_i) prod conj(M_(b_j)),   sum a_i = sum b_j <= k.
```

Homometric pairs share every `|M_m|^2`. The study asks whether the first
moment order `K_ph` at which a pair separates equals the smallest total charge
`K_inv` of a monomial whose real part differs, and what that implies for this
repository's 63-site pair.

## Results

`python noise_order.py dictionary --output results.json` reproduces
[results.json](results.json). It enumerates every pair of subsets of `Z_N`
(`6 <= N <= 14`, sizes `3..N/2`) with equal difference multisets that are not
related by translation or reflection, at `q = 2 pi / N`, with `t = 1/2` and
`t = 3/10`.

- 86 nontrivial pairs; `K_ph = K_inv` for all 86.
- 84 pairs first separate at order 2, through `Re(M_2 conj(M_1)^2)`.
- 2 pairs first separate at order 3, through `Re(M_3 conj(M_2) conj(M_1))`.
- No pair is unseparated through order 8.

`python noise_order.py identity` checks an exact second-moment identity for
homometric pairs:

```text
E_A[I^2] - E_B[I^2] = -2 t^4 (1 - t^2) [Re(M_2 conj(M_1)^2)_A - Re(M_2 conj(M_1)^2)_B].
```

It comes from two site-charge patterns: `(2, -1, -1)` with weight `t^6`, and
`(1, 1, -1, -1)` with weight `t^4`, whose merged-site inclusion-exclusion term
contributes `-t^4`. The script reproduces it to about 40 digits at
`t = 0.3, 0.5, 0.9` on four pairs. For a general symmetric iid phase law the
same derivation gives the coefficient `2[phi(2) phi(1)^2 - phi(1)^4]`; only
the Gaussian case was checked.

## A general separation law

The two observations above are special cases of one formula. Write
`phi(m) = E exp(i m theta)` for any iid phase law, and

```text
l_m = [x^m] log( sum_a phi(a) x^a / a! ),     c_K = [x^K] exp( sum_{m>=1} l_m M_m x^m ).
```

If two phasor multisets agree in every charge-neutral monomial of charge below
`K`, then

```text
E_A[I^K] - E_B[I^K] = (K!)^2 ( |c_K^A|^2 - |c_K^B|^2 ).
```

Derivation sketch: `E[I^K] = (K!)^2 [x^K y^K] prod_j F(x z_j, y conj z_j)` with
`F(a, b) = E exp(a u + b conj u)`, `u = exp(i theta)`. Taking logarithms turns the
product into `exp(sum L_ab x^a y^b M_(a-b))`. A product of these factors has
positive charge equal to the full `x`-degree `K` only when every factor is pure
(`a = 0` or `b = 0`), so the charge-`K` part factors as
`[x^K] exp(sum l_m M_m x^m)` times its conjugate. All lower-charge terms cancel
by hypothesis.

`python separation_law.py law results.json` checks the law against direct
moments for all 86 pairs at `t = 0.3, 0.5, 0.9` and for a uniform phase law on
`[-a, a]` (`a = 0.7, 1.9`); the worst relative mismatch is about `5e-67`. With
the Gaussian law, `l_2 = -t^2 (1 - t^2) / 2` and
`l_4 = -t^4 (1 - t^2)^3 (t^6 + 3t^4 + 6t^2 + 6) / 24`. Since `M_1 = 0` for this
repository's pair, `D_4 = (4!)^2 l_4 l_2^2 * dRe(M_4 conj(M_2)^2)`, which with the
gap `-455015761/120000` gives exactly
`(455015761/20000) t^8 (1 - t^2)^5 (t^6 + 3t^4 + 6t^2 + 6)` (checked with sympy).
The derivation is written here, not formalized.

## Pairs hidden to high order

`python separation_law.py survey 22` counts the first differing charge over all
23,168 nontrivial homometric pairs in `Z_N`, `N <= 22`:

| first differing charge | 2 | 3 | 4 | 5 | 6 | 7 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| pairs | 22,138 | 866 | 131 | 31 | 1 | 1 |

No pair agreed in every charge-neutral monomial through charge 8, and no pair
had a differing invariant while `|c_K|^2` agreed identically in `t`.

The order-6 and order-7 pairs share a structure that generalizes. With
`N = 3k`, `H = 3 Z_N` and `T` a subset of `Z_k` that is not a translate of its
reflection, set `A = H u (1 + 3T)` and `B = H u (1 - 3T)`. For `k` not dividing
`m`, `M_m(H) = 0` and `M_m(B)` is a fixed phase times `conj M_m(A)`, so every
charge-neutral monomial of charge below `k` has equal real part. The two sets
are therefore homometric and noncongruent, and their single-frequency
intensity moments agree below order `k` for every iid phase law. The family
was written down before being tested; `python separation_law.py family` checks
`k = 6..10` (relative gaps below order `k` at the `1e-70` level, nonzero order-`k`
gaps, and the separation law reproducing them). The order-`k` gaps are tiny in
relative terms (about `1e-7` at `k = 6` and `1e-15` at `k = 10`), so these pairs
are mathematically hidden to high order and are not practical measurement
targets.

## Consequence for this repository's pair

Both 63-site lists have `M_1 = 0` at `q = pi/3` (the
[geometry record](../../formal/GEOMETRY.md)). That removes every order-2 and
order-3 monomial that could differ. The first differing charge-neutral
monomial is `Re(M_4 conj(M_2)^2)`, whose exact gap `-455015761/120000` is the
source of the fourth-order coefficient. With the Minkowski factorization
`M_m(A) = M_m(U) M_m(V)` and `M_m(B) = M_m(U) conj(M_m(V))`, up to a phase
that cancels in every charge-neutral monomial, that gap is `-2 Im(T_U) Im(T_V)` for `T = M_4 conj(M_2)^2`:
`-2 x (-364.865933471) x (-5.19615242271) = -3791.79800833`.

So the fourth-order-only separation is a special case of the general rule, not
the generic behavior: generic homometric pairs separate at the second moment.

## A negative check

`python noise_order.py three-factor` tests whether a third factor `W = {0, a, c}`
can push the first mismatch beyond order 4. When `M_2(W) = 0` the two
three-factor sets have identical laws, but each is a global phase rotation of
the other's phasor multiset, so nothing nontrivial is hidden. When
`M_2(W) != 0`, the first mismatch stays at order 4.

## Limits and related work

- Integer subsets of `Z_N` at `q = 2 pi / N`, sizes at most 7, `N <= 14`; the
  separation tolerance is `1e-18` relative.
- The identity, the separation law and the coset-family argument are checked
  numerically and written as derivations; none is formalized. The family was
  checked numerically only for the Gaussian law at `t = 0.6`.
- An earlier version of the family check compared absolute residuals with a
  fixed threshold below the arithmetic's resolution and mislabelled correct
  instances as failures; the check now uses relative residuals.
- Homometric subsets of `Z_N` are also studied as Z-related sets in
  mathematical music theory (for example Mandereau, Ghisi and Amiot,
  *Z-relation and homometry in musical distributions*, 2012), and random-phasor
  intensity moments go back at least to Barakat's work listed in
  [priority.md](../../docs/priority.md). Neither comparison was completed here.
- Bispectral products already appear in photon-correlation phase retrieval
  (Bojer et al., equation 16, listed in [priority.md](../../docs/priority.md)),
  and Grunbaum-Moore use higher-order invariants for cyclotomic homometric sets.
  The order-to-charge correspondence here is a candidate organizing statement
  for this single-frequency phase-noise model, not a priority claim.

The study was developed with AI assistance under the maintainer's direction;
its checks are same-workflow reproductions, not independent review.
