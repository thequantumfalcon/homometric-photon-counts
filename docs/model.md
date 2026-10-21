# Model and notation

The primary model has two fixed sets of 63 unit phasors, independent centered Gaussian site phases, a time-local conditional Poisson detector, common background, and known parameters for the stated testing result. The intensity satisfies $0\le I\le3969$.

Use $s$ for phase variance, $t=e^{-s/2}$, and $x=t^2=e^{-s}$. The reference point is $s=2\log2,t=1/2,x=1/4$. Some formal statements parameterize the polynomial directly by a variable named `t` or use `exp(-s)` as a generic point in $(0,1)`. The physical substitution must be checked explicitly; variable names alone are not an identification proof.

The intensity moment differences $D_k=E_A[I^k]-E_B[I^k]$ obey $D_0=\cdots=D_3=0$ and

$$D_4(t)=\frac{455015761}{20000}t^8(1-t^2)^5(t^6+3t^4+6t^2+6)>0.$$

For $N\mid I\sim\operatorname{Poisson}(b+\eta I)$, the fourth falling-factorial moment difference equals $\eta^4D_4(t)$. Common background cancels because the first three intensity moments match. Arbitrary preprocessing, detector saturation, dead time, dependent site phases, unequal backgrounds, or drifting parameters require additional arguments.

The fixed testing experiment pools counts at least 12 into one bin. It assumes iid snapshots and known $s,\eta,b$. Its lower bound does not apply to the richer unbinned observation, and its sufficient count does not establish a feasible measurement duration.

Archived exposure, calibration and dependence extensions retain their own hypotheses. In particular, the public `homometric-motion` project studies a different spring/OU exposure model. Neither its sample counts nor its formal declarations are automatically premises of this repository.
