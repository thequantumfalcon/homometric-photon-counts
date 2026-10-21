# Model and notation

The primary model has two fixed lists of 63 unit phasors, independent centered Gaussian site phases, a time-local conditional Poisson detector, common background, and known parameters for the stated testing result. The intensity satisfies $0\le I\le3969$.

Use $s$ for phase variance, $t=e^{-s/2}$, and $x=t^2=e^{-s}$. The reference point is $s=2\log2,t=1/2,x=1/4$. The [geometry extension](../formal/GEOMETRY.md) proves the exponential substitution and the resulting polynomial identity. The [Gaussian extension](../formal/GAUSSIAN.md) derives an exact finite-sum expression for every intensity moment. The [concrete certificates](../formal/CERTIFICATES.md) evaluate the proved recurrence to establish the specific 63-site moment identities below.

The intensity moment differences $D_k=E_A[I^k]-E_B[I^k]$ obey $D_0=\cdots=D_3=0$ and

$$D_4(t)=\frac{455015761}{20000}t^8(1-t^2)^5(t^6+3t^4+6t^2+6)>0.$$

For $N\mid I\sim\mathrm{Poisson}(b+\eta I)$, the fourth falling-factorial moment difference equals $\eta^4D_4(t)$. Common background cancels because the first three intensity moments match. Arbitrary preprocessing, detector saturation, dead time, dependent site phases, unequal backgrounds, or drifting parameters require additional arguments.

The formal construction uses a finite product of centered Gaussian laws with variance $s$, the explicit phase lists, and a measurable Poisson mixture with rate $b+\eta I$. It proves $0\le I\le3969$ for both geometries and integrability of every intensity power. The final theorem `PhotonConcreteSeparation.count_laws_distinct` proves the concrete low-order moment matches and fourth-gap identity and uses them to establish count-law distinction; these moment values are no longer hypotheses. The [joint snapshot extension](../formal/JOINT_MODEL.md) constructs phases and counts on one probability space, proves the conditional Poisson law given intensity, and identifies its count marginal with this mixture. The [archive-input bridge](../formal/ARCHIVE_INPUT.md) now parses the saved exact phase arrays and proves that their evaluations are permutations of the formal lists. External file selection and byte binding are checked separately. The coordinate-to-exponential derivation remains computational, and transporting the count law to the archived site ordering still requires reindexing; neither is a physical calibration result.

The fixed testing experiment pools counts at least 12 into one bin. It assumes iid snapshots and known $s,\eta,b$. Its lower bound does not apply to the richer unbinned observation, and its sufficient count does not establish a feasible measurement duration.

Archived exposure, calibration and dependence extensions retain their own hypotheses. In particular, the public `homometric-motion` project studies a different spring/OU exposure model. Neither its sample counts nor its formal declarations are automatically premises of this repository.
