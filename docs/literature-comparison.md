# Equation-level comparison with classical work

Updated 23 October 2026. This note narrows the [priority assessment](priority.md); it does not establish historical novelty or replace specialist review. It compares the original iid Gaussian phase and conditional Poisson model, not the later optical studies. Earlier evidence and access receipts remain unchanged.

The result being compared is specific. For unit phasors $z_{G,j}$, independent $Z_j\sim N(0,1)$ and $t=e^{-s/2}$, put

$$F_G=\sum_jz_{G,j}e^{i\sqrt{s}Z_j},\quad I_G=|F_G|^2,\quad M_{G,r}=\sum_jz_{G,j}^r.$$

At a common clean null $M_{A,1}=M_{B,1}=0$, with equal cardinality and $|M_{A,r}|=|M_{B,r}|$ for $r=2,3,4$, the [retained derivation](../evidence/homometric-photon-counts/science_completion/homogeneous_control/homogeneous_control_proof.txt) gives equal first three intensity moments and

$$\mathbb E[I_A^4]-\mathbb E[I_B^4]
=6\kappa_{4,0}(t)\kappa_{2,0}(t)^2\,(T_A-T_B),\qquad
T_G=\operatorname{Re}(M_{G,4}\overline{M_{G,2}}^{\,2}),$$

$$\kappa_{2,0}=t^4-t^2,\qquad
\kappa_{4,0}=t^{16}-4t^{10}-3t^8+12t^6-6t^4.$$

The [concrete formal proof](../formal/CERTIFICATES.md) verifies the 63-site specialization. The general selection argument above and historical priority are separate questions.

## Homometry and the Z-relation

[Jedrzejewski and Johnson (2013), section 1 and Proposition 1](https://arxiv.org/html/1304.6608v1) identify interval counts with coefficients of the Patterson product $P(x)P(x^{-1})$ in a finite cyclic group. [Callender and Hall's 2008 author handout, section 4](https://myweb.fsu.edu/ccallender/z-relationhandout.pdf), also treats real and circular positions, Fourier magnitudes, and the spectral-unit formulation. These inspected sources make the geometric ambiguity and the Fourier-magnitude criterion established background.

Here the direct reduction can be written without choosing a cyclic modulus. Let $\mu_S=\sum_{x\in S}\delta_x$, and let $\widetilde\mu_S$ reflect this measure through zero. With the repository's motif $C$ and $V=\{0,31,63\}$,

$$\mu_A=\mu_C*\mu_V,\qquad
\mu_B=\delta_{63}*\mu_C*\widetilde\mu_V.$$

The translates are disjoint, so these convolutions give unit-weight sets rather than multiplicities at coincident sites. Commutativity then gives

$$\mu_A*\widetilde\mu_A
=\mu_C*\widetilde\mu_C*\mu_V*\widetilde\mu_V
=\mu_B*\widetilde\mu_B.$$

Equivalently, for $H_S(q)=\sum_{x\in S}e^{iqx}$,

$$H_A(q)=H_C(q)H_V(q),\qquad
H_B(q)=e^{63iq}H_C(q)\overline{H_V(q)}.$$

This is our explicit substitution into the classical factor-reflection mechanism. It directly establishes equal clean diffraction at every real frequency. Thus homometric construction by this mechanism is not a candidate new method. Cyclic interval equality alone would not establish equality of real-line differences; the displayed real-measure identity does. Neither identity specifies random phase perturbations or the order at which their intensity moments separate.

## Structural correlations and observed moment order

[Jaming and Kolountzakis (2003), section 2.1, equation (2.1), and section 3.1](https://nyjm.albany.edu/j/2003/9-12p.pdf) express correlation data through products of Fourier coefficients whose arguments sum to zero. The finite-measure version follows by expanding the sums. Taking arguments $2q,2q,-4q$ gives $M_2^2\overline{M_4}$; its real part is exactly $T$. This is our substitution, not a claim made there about this experiment. It establishes that the selected structural invariant has a classical bispectral form.

The same paper's section 3.4, pp. 160–161, states the Grünbaum–Moore reconstruction results with their original theorem numbers. We inspected that account, but did not recover the complete [Grünbaum–Moore 1995 article](https://doi.org/10.1107/S0108767394009827) in this pass. A search-indexed public mirror was identified; direct retrieval timed out. Indexed passages are not a full-text review.

The measurement orders must remain distinct: $T$ is third order in clean structural Fourier amplitudes; $I^4$ is fourth order in random intensity and eighth order in random field factors. Having full spatial correlation data is a different experiment from observing one noisy intensity at one frequency. A reconstruction theorem for the former does not automatically give the Gaussian coefficient, the photon-count law, or a sample bound for the latter.

## Finite random phasors and wrapped-normal moments

[Ainsleigh (2017), publisher abstract](https://epubs.siam.org/doi/10.1137/16M1082019), describes higher moments of quadratic forms in independent wrapped variables using characteristic functions. The full text remains unavailable here. The exact fit to that problem class is our algebraic observation: with $w_j=e^{i\sqrt{s}Z_j}$ and column vector $a_j=\overline{z_j}$,

$$I=w^*(aa^*)w,\qquad
\mathbb E[w_j^u\overline{w_j}^{\,v}]=t^{(u-v)^2}.$$

The deterministic matrix is Hermitian and rank one; the wrapped variables are independent. General computation of these moments is therefore established prior work. The abstract does not permit an equation-number comparison of its fourth-moment formula, simplification at $\sum_jz_j=0$, or exact coefficient. Those are concrete remaining checks, not evidence that the specialization is new.

There is an accessible full-text finite-phasor comparison: [Shimizu (2025), equation (1), Appendix A equations (A2a–b), (A3), and (A14)](https://os.copernicus.org/articles/21/2233/2025/os-21-2233-2025.html). His convention uses $A_je^{-i\Theta_j}$. Set $A_j\equiv1$, mean lag $\phi_j=-\arg z_j$, phase spread $\sigma_j^2=s$, and $N=63$. The symmetry of the centered Gaussian phase gives our field law. The product of his centering factors equals one at the common null, since $\mathbb EF=tM_1=0$. Equation (A14)'s factor $e^{-k^2s/2}=t^{k^2}$ supplies the same single-site Fourier coefficients.

This substitution directly recovers the exact finite random field within an earlier framework. It does not require the many-source Gaussian approximation discussed elsewhere in that paper. Extracting and simplifying the eighth field moment remains an additional calculation; the inspected formulas do not state this homometric selection identity.

## Barakat's photocount statistics

[Barakat (1983), publisher abstract](https://opg.optica.org/josa/abstract.cfm?uri=josa-73-9-1138), explicitly covers photoelectron distributions and moments for an arbitrary fixed number of independent nonuniform-phase weak scatterers, followed by a random-number extension. This is a direct predecessor for the broad finite-scatterer counting problem. The fixed-number case is the relevant lead here.

The full article remained inaccessible on 23 October; the equation-navigation link did not expose its formulas. Earlier notes record a publisher preview. Neither that preview nor the abstract establishes the exact phase-law hypotheses needed to substitute $z_je^{i\sqrt{s}Z_j}$ into a numbered result. We therefore do not attribute uninspected Gaussian or homometric cancellation formulas to Barakat, or claim that his work excludes them. The [earlier dossier](../evidence/homometric-photon-counts/science_completion/literature/iid_gaussian_homometry_novelty_comparison.txt) also retains the unresolved 1981 and 1988 leads.

For comparison once the article is available, the repository's detector step is explicit. If $N\mid I\sim\operatorname{Poisson}(b+\eta I)$, then

$$\mathbb E[(N)_r]=\mathbb E[(b+\eta I)^r].$$

Common $b$ and matching intensity moments below order four give the fourth factorial-count gap $\eta^4(\mathbb E[I_A^4]-\mathbb E[I_B^4])$. This standard mixed-Poisson transfer is not a candidate new principle. It requires the stated conditional detector model; an exposure-integrated random rate would need its own intensity calculation.

## What is established and what still needs comparison

| Question | Assessment after the explicit substitutions |
| --- | --- |
| Is the factor-reflection homometry mechanism new? | No novelty claim: the real-measure substitution above supplies the classical algebraic reduction. |
| Is the separating quantity a new structural invariant? | No novelty claim: it is a real diagonal bispectral quantity. |
| Is exact finite Gaussian-phasor moment calculation new? | No novelty claim: the field is contained in an inspected finite-phasor framework and in the quadratic-form problem class. |
| Do the inspected earlier formulas directly state this first-three/fourth cancellation and coefficient? | No such statement was identified in the inspected material. The repository adds an explicit partition classification and concrete evaluation; whether this specialization was previously obtained remains unresolved. |
| Are the root certificate, testing bounds, or formalization implied by those comparisons? | No such implication was established. Each has its own observation assumptions and proof scope. |

The remaining reduction test is precise: inspect Barakat's and Ainsleigh's full formulas under the substitutions above, impose the clean null and shared harmonic magnitudes, and collect the surviving eighth-field terms. In the repository's derivation the only unequal terms have charges $(4,-2,-2)$ and $(-4,2,2)$, with coefficient $6\kappa_{4,0}\kappa_{2,0}^2$. Check whether an earlier theorem already gives that simplification and its sign, then compare any explicit pair or calibration specialization. Grünbaum–Moore's complete article remains a separate higher-correlation comparison. A bounded search, an algebraic specialization, and a machine-checked concrete theorem cannot establish absence of earlier work.
