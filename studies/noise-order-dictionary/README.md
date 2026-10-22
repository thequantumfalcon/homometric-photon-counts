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
- The identity is checked numerically, not formalized.
- Bispectral products already appear in photon-correlation phase retrieval
  (Bojer et al., equation 16, listed in [priority.md](../../docs/priority.md)),
  and Grunbaum-Moore use higher-order invariants for cyclotomic homometric sets.
  The order-to-charge correspondence here is a candidate organizing statement
  for this single-frequency phase-noise model, not a priority claim.

The study was developed with AI assistance under the maintainer's direction;
its checks are same-workflow reproductions, not independent review.
