# A quantitative model-error budget for the fixed count test

The reference 13-bin test has a conservative extension to imperfect conditional count laws. At $t=1/2$, $\eta=1/20$, $b=0$, it still guarantees each error below 5% after **204,799,753,446,338 observations** if every next-bin conditional law is within **$3\times10^{-9}$ total variation** of the corresponding reference law, almost surely given the observed past.

This is an analytic extension with an [exact rational certificate](validation/model_tolerance.json), conditional on the retained probability enclosures. It is not a Lean theorem, a measured hardware tolerance, a smaller sample bound, or evidence that a laboratory can meet this requirement. The numeric bound concerns probability distributions on the 13 bins; it is not a tolerance in radians, gain, time or spatial distance.

## Statement and proof

Let $P_A,P_B$ be the reference bin laws. Counts $0,\ldots,11$ retain individual bins and counts at least 12 share the final bin. The [retained certificate](../evidence/continuation-2026-10-20/multibin/certificate.json) supplies fixed rational scores $w_j$ and $d>0$ such that

$$E_{P_A}e^{-w}\leq1-d,\qquad E_{P_B}e^w\leq1-d.$$

The decision is A when the sum of scores is nonnegative and B otherwise. Write $R=\max_j w_j-\min_j w_j$. Every $|w_j|\leq1$, so the mean-value theorem and $e<3$ give

$$\operatorname{osc}(e^w),\operatorname{osc}(e^{-w})\leq3R.$$

For probability vectors $P,Q$, use $\operatorname{TV}(P,Q)=\tfrac12\sum_j|P_j-Q_j|$. The positive and negative parts of $Q-P$ each have mass TV. Subtracting the minimum of a bounded function and bounding its positive contribution proves

$$E_Q f\leq E_P f+\operatorname{TV}(P,Q)\operatorname{osc}(f).$$

Under hypothesis G, suppose each next-bin conditional law $Q_{G,i}(\cdot\mid X_1,\ldots,X_{i-1})$ is within $\delta$ of $P_G$, almost surely. The appropriate conditional exponential moment is then at most $c=1-d+3R\delta$. Repeated conditional expectation gives

$$E_A e^{-\sum_iw(X_i)}\leq c^m,\qquad E_B e^{\sum_iw(X_i)}\leq c^m.$$

Markov's inequality bounds both classification errors by $c^m$. If $\delta\leq d/(6R)$, then $0<c\leq1-d/2$ and $c^m\leq e^{-md/2}$. The original certified count $m_0=102399876723169$ satisfies $m_0d\geq3$. Thus $m=2m_0$ gives each error at most $e^{-3}<1/20$.

The exact checker verifies the sufficient choice $\delta=3/10^9\leq d/(6R)$. For orientation, $d\approx2.92969\times10^{-14}$, $R\approx1.32219\times10^{-6}$ and $d/(6R)\approx3.69298\times10^{-9}$. These decimals are illustrative; rational inequalities determine the result. This radius is sufficient and conservative, not a necessary or optimal tolerance.

## What dependence is allowed

Independent but nonidentically distributed snapshots are covered if each law satisfies the stated bound. Dependent snapshots are covered only by the stronger **conditional-on-every-observed-past** hypothesis above. Closeness of individual marginal laws is insufficient: repeating a single random observation forever preserves each marginal exactly but supplies no new independent evidence. No significance test on a finite sample establishes the conditional-law assumption for all histories.

## Parameter perturbations within the Gaussian/Poisson family

For a restricted model, a coupling converts parameter errors into a sufficient TV budget. Suppose the perturbed snapshot still uses 63 unit phasors, independent centered Gaussian phases of variance $s'$, and a Poisson rate $b'+\eta'I'$. Couple the two phase vectors using the same standard normals. Let $\epsilon=\max_j|z'_j-z_j|$ be the maximum chord distance between corresponding unit phasors, and $\Delta\sigma=|\sqrt{s'}-\sqrt{s}|$. Then

$$E|I'-I|\leq 2\cdot63^2(\epsilon+\Delta\sigma).$$

Indeed both field magnitudes are at most 63, their difference is bounded by the sum of phasor differences, $|e^{iu}-e^{iv}|\leq|u-v|$, and $E|Z_j|\leq\sqrt{E Z_j^2}=1$. The two rates consequently satisfy

$$E|\lambda'-\lambda|\leq |b'-b|+3969|\eta'-\eta|+7938\eta(\epsilon+\Delta\sigma).$$

For deterministic Poisson rates $a,c$, couple a Poisson variable of rate $\min(a,c)$ with an independent residual of rate $|a-c|$. The chance of different counts is at most $1-e^{-|a-c|}\leq|a-c|$. Applying this construction conditionally on the coupled phases bounds count-law TV by the expected rate difference. Binning cannot increase it. At the reference gain $\eta=1/20$, a sufficient parameter condition is therefore

$$|b'|+3969|\eta'-1/20|+\frac{3969}{10}(\epsilon+|\sqrt{s'}-\sqrt{2\log2}|)\leq3\times10^{-9}.$$

The checker records exact radii when **only one quantity changes**. These are $3\times10^{-9}$ for background, approximately $7.56\times10^{-13}$ for gain, and approximately $7.56\times10^{-12}$ for either maximum phasor chord error or phase standard deviation. Simultaneous errors must share the displayed budget; each cannot consume its whole radius. These are conservative sufficient conditions, not experimentally necessary tolerances. Unequal amplitudes, non-Gaussian phase laws and non-Poisson detection need other bounds. Applying this argument to varying or dependent acquisitions requires its assumptions and bounds conditionally on the past, not merely after averaging over an entire run. This is a neighborhood for the specified **test guarantee**, not a radius preserving exactly four blind gains.

## Reproduce and use responsibly

```sh
python tools/check_model_tolerance.py --output build/model-tolerance.json
```

The checker verifies the evidence bindings, encloses score exponentials by exact Taylor sums with geometric tail bounds, maximizes expectations over the retained probability boxes intersected with the simplex, and checks the contraction/radius/sample inequalities using rational arithmetic. It does not reconstruct the physical model or replace the existing Arb probability reconstruction. Its unit checks include a separate enumeration of probability-polytope vertices and rejection of infeasible boxes.

An experiment needs a justified bound relating geometry, phase, detector and drift errors to this distributional budget, or a newly derived less conservative test. The existing [measurement and preanalysis protocol](../evidence/homometric-photon-counts/science_frontier/review_and_experiment/external_review_and_physical_test.txt) describes the required records and controls. For an initial demonstration, an attainable parameter regime should be selected and its predictions recomputed; the enormous reference sample count is not an acquisition recommendation.
