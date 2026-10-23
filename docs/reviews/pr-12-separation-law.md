# Review of draft PR #12: separation law and noise-order dictionary

Reviewed 23 October 2026 at head
[`1f310ad92286398a44b68183d245ef639902ad7e`](https://github.com/thequantumfalcon/homometric-photon-counts/commit/1f310ad92286398a44b68183d245ef639902ad7e)
of [PR #12](https://github.com/thequantumfalcon/homometric-photon-counts/pull/12).
**Disposition: retain as a draft; do not merge this revision.** The central
coefficient derivation survived this bounded review, and the small dictionary
reproduced. A separate, broadly worded three-factor conclusion has an explicit
counterexample. Dependency, survey-evidence and automated-check gaps also remain.
These findings concern the proposed study, not the accepted 63-site result.

This was a fresh source inspection and computational replay with AI assistance
under the maintainer's direction. It is not external human review, a formal
proof, an interval certificate or a priority determination. The
[replay receipt](pr-12-replay.json) records versions, source hashes, commands and
limits. The checked-out main branch and byte-pinned evidence were not replaced
with PR files.

## Mathematical assessment

The separation law concerns finite multisets of **unit** phasors, equal site
counts, independent identically distributed site phases, and unnormalized
intensity `I = |sum z_j exp(i theta_j)|^2` at one fixed frequency. For an arbitrary
phase law, equality of the full complex charge-neutral monomials below charge
`K` is required. Equality of real parts suffices when the phase law is symmetric
about some point. These distinctions are present in the reviewed revision.

The coefficient argument is sound at the level of the written derivation:
independence gives a product generating function; its logarithm contributes
harmonics `M_(a-b)`; mixed factors have charge strictly below their total
`x`-degree; and only pure `x` and pure `y` factors survive in the charge-`K`
part. The resulting diagonal coefficient is `|c_K|^2`. Bounded unit phasors
justify the generating-function expansion near zero; it can also be read as
an identity of truncated formal series. This review did not formalize that
argument or validate a claim of historical originality.

The coset-family argument has meaningful restrictions: iid phase-law symmetry
and `gcd(r,k)=1` at `q=2*pi*r/(3k)`. Independent controls reproduced order-six
separation for `k=6,r=1`, and order-three separation for `r=2` (about 0.291%
relative). The supplied asymmetric-law controls separate at order two.
For the geometric homometry proof, explicitly apply the Fourier identities at
`r=1`, which samples every character of `Z_(3k)`. The condition `gcd(r,k)=1`
alone can permit `3 | r`, so the observed harmonics at that frequency need not
sample every character. The family remains homometric; that proof step should
not rely on an incomplete character set.

The general separation identity does **not** by itself say that every differing
invariant produces a nonzero gap at that same moment order: the resulting weighted
combination can cancel, and the phase law matters. The finite Gaussian
dictionary supports an observation about its tested pairs and noise parameters.

## Counterexample to the broad three-factor conclusion

The PR's negative-check paragraph says that when `M_2(W) != 0`, the first
mismatch stays at order four. Its program tests only four selected factors.
The unrestricted sentence is false, even with three sites in `W` and the
original iid Gaussian model.

Let `A,B` be the repository's original 63-site structures and retain `q=pi/3`.
Choose

```text
W = {0, 241/2, 241}.
```

The corresponding phasors are `1, exp(i*pi/6), exp(i*pi/3)`, so exactly

```text
M_2(W) = 1 + i*sqrt(3) != 0,
M_4(W) = 1 + exp(2*pi*i/3) + exp(4*pi*i/3) = 0.
```

The translated copies are disjoint: each original structure lies in `[0,93]`
and the copy spacing is `120.5`. Thus `A+W` and `B+W` each have 189 distinct
unit-amplitude sites. Convolution of their directed-difference multisets
preserves homometry. Harmonics multiply under this addition, so both enlarged
structures have `M_1=0` and `M_4=0`. Every real neutral invariant through charge
four agrees; in particular, the fourth-order separating invariant vanishes.
Consequently `D_1=D_2=D_3=D_4=0` for iid Gaussian site phases.

The example is not an all-order rotation ambiguity. From the exact harmonic
values in [PhotonGeometry.lean](../../formal/PhotonGeometry.lean),

```text
dRe(M_5 conj(M_2) conj(M_3)) for the original pair
    = -124577746657/288000000.
M_5(W) conj(M_2(W)) conj(M_3(W)) = 2(1-sqrt(3)).
```

At `t=1/2`, the logarithmic coefficients are
`l_2=-3/32`, `l_3=27/1024`, and `l_5=779247/268435456`.
With `M_1=M_4=0`, `c_5=l_5*M_5+l_2*l_3*M_2*M_3`. The common norm terms
cancel, giving the following nonzero value by the reviewed separation identity:

```text
D_5(1/2) = [7863223663287409599/43980465111040000] * (1-sqrt(3))
         = -130.8826366040251256404055766394...
```

This is an exact algebraic consequence of the stated harmonic tables and
coefficient identity, not a new Lean theorem. An 80-digit direct moment replay
agreed with that expression to absolute error below `1.2e-68`; the relative
fifth-moment gap was about `1.9132e-11`. The direct residuals through order four
were below `1e-79` relative. Numerical residuals alone are not the reason for
the exact zero claims above.

The rational coefficient can be reproduced with standard-library Python:

```python
from fractions import Fraction as F
from math import factorial

# Represent a+b*alpha by (a,b), with alpha=i*sqrt(3).
def mul(x, y):
    return x[0]*y[0]-3*x[1]*y[1], x[0]*y[1]+x[1]*y[0]
def conj(x):
    return x[0], -x[1]
def invariant(m2, m3, m5):
    return mul(mul(m5, conj(m2)), conj(m3))[0]
a = invariant((F(71,40), F(413,40)), (F(-1), F(1183,400)),
              (F(8029567,2880000), F(-8336939,2880000)))
b = invariant((F(131,8), F(171,40)), (F(1), F(-1183,400)),
              (F(-13585,4608), F(-2727751,960000)))
f = [F(1,2)**(m*m)/factorial(m) for m in range(6)]
ell = [F(0)]*6
for m in range(1,6):
    ell[m] = f[m] - sum((j*ell[j]*f[m-j] for j in range(1,m)), F(0))/m
assert a-b == F(-124577746657,288000000)
coefficient = 4*factorial(5)**2*ell[5]*ell[2]*ell[3]*(a-b)
assert coefficient == F(7863223663287409599,43980465111040000)
print(coefficient)  # D5 = coefficient * (1-sqrt(3))
```

For a direct numerical replay, obtain the reviewed PR source at the pinned head,
install its pinned `mpmath`, and run the following from
`studies/noise-order-dictionary/`:

```python
import mpmath as mp
from separation_law import gauss, moment
mp.mp.dps = 80
q = mp.pi/3
theta = mp.asin(1/(5*mp.sqrt(3)))
varphi = -mp.asin(1/(8*mp.sqrt(3)))
U = [mp.mpf(30)]
for j in range(10):
    U += [3*j+1+3*(-1)**j*theta/mp.pi,
          3*j+3*(0 if j < 2 else (-1)**j*varphi)/mp.pi]
W = [0, mp.mpf('120.5'), 241]
za = [mp.expj(q*(u+v+w)) for u in U for v in (0,31,63) for w in W]
zb = [mp.expj(q*(u+v+w)) for u in U for v in (0,32,63) for w in W]
for K in range(1,6):
    ea, eb = moment(za, gauss(mp.mpf('.5')), K), moment(zb, gauss(mp.mpf('.5')), K)
    print(K, mp.nstr(ea-eb, 35), mp.nstr(abs(ea-eb)/(1+abs(ea)), 8))
expected = mp.mpf(7863223663287409599)/43980465111040000*(1-mp.sqrt(3))
assert abs((ea-eb)-expected) < mp.mpf('1e-60')
```

## Reproduction results and gaps

Replays used Python 3.11.9 on Windows, the PR's pinned `mpmath==1.4.1`, and
NumPy 2.2.6 for the survey. Commands below ran in the staged study directory;
outputs went to fresh destinations. Every command completed successfully,
and its printed numerical result was inspected.

| Command | Observed result |
| --- | --- |
| `python noise_order.py dictionary --output ../../dictionary-replay.json` | All 86 pairs agree in first separating charge/order; 84 at order two, two at order three. JSON equals the saved result after newline normalization. |
| `python noise_order.py identity` | All 12 checks agree; maximum absolute discrepancy below `3e-39`. |
| `python noise_order.py three-factor` | Reproduces the four advertised examples; does not establish the general sentence refuted above. |
| `python separation_law.py law results.json` | 86 pairs times five phase laws; worst relative mismatch `5.29e-67`. |
| `python separation_law.py family` | `k=6..10`: homometric and noncongruent; largest relative residual below order `k` is `8.06e-70`; nonzero order-`k` gaps and matching predictions. |
| `python separation_law.py brute` | 54 cases; worst relative discrepancy `3.71e-69`. This enumeration is a second algorithm in the supplied source, not an external reviewer. |
| `python separation_law.py asymmetric` | Gaussian cases first differ at orders six/seven; both asymmetric laws first differ at order two, by roughly 2–3%. |
| `python separation_law.py survey 14` | Reproduces `{2: 84, 3: 2}`. The full `survey 22` run was outside this bounded review. |

An additional 80-digit control checked the general law at `K=2` under an
asymmetric two-point phase distribution for the homometric pair
`{0,1,2,5}`, `{0,1,3,4}` in `Z_8`; its residual was below `1.2e-80` after
division by `1+abs(D_2)`.

The following gaps must be fixed or the associated claims narrowed:

1. **Declare all dependencies.** `survey` imports NumPy, but the study's
   `requirements.txt` contains only `mpmath==1.4.1`. The survey currently depends
   on an undeclared ambient package. The README also mentions symbolic checks
   without shipping their script or dependency record.
2. **Distinguish survey outputs from stronger conclusions.** The shipped
   `survey` computes first differing invariant charges using double precision
   and a `1e-7` threshold. It does not compute `c_K`, direct moments or an exact
   polynomial in `t`. It therefore does not reproduce the claim that none of
   the 23,168 pairs has a first-charge cancellation identically in `t`. The
   reported separate 50-digit recheck of 164 high-order pairs has no shipped
   command or result receipt. This review did not verify either assertion.
3. **Make failed checks fail.** Most study commands only print residuals,
   Boolean results or tallies. Add explicit numerical thresholds, expected
   counts and nonzero exits for failures, with regression tests covering
   symmetry/frequency violations and the three-factor counterexample.
4. **Run the new checks in CI.** The successful
   [head workflow](https://github.com/thequantumfalcon/homometric-photon-counts/actions/runs/39870654710)
   runs the established capsule and Arb checks. Its pinned workflow does not
   invoke either new study script. Green status does not validate this study.
5. **Complete the comparison and integration review.** Resolve the merge
   conflict, incorporate the [primary-literature comparison](../priority.md),
   keep derivations distinct from numerical surveys and formal certificates,
   and re-run the relevant checks on the integrated revision. GitHub reported
   this head as a conflicting draft with no submitted reviews when inspected.

Narrowing the negative-check paragraph to its four actual examples would remove
that particular overstatement. A stronger revision could include the explicit
fifth-order example with its own derivation and checked source. Neither route
requires claiming formalization or novelty. Reassess the draft after the listed
mathematical and reproducibility issues are addressed; this review does not
authorize treating the proposed study as an accepted result on main.
