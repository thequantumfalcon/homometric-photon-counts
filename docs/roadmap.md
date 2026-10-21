# Research roadmap

| Open target | Evidence needed to close it |
| --- | --- |
| Extend formal coverage beyond count-law distinction | Formally bind the phase definitions to archived coordinates; formalize the root and testing certificates and their connection to the decision theorem |
| Useful larger root-stability neighborhoods | Improve the [certified rectangle](root-stability.md), whose radii $10^{-23}$ in $t$ and $10^{-20}$ in common background are deliberately conservative; assess tolerances relevant to a specified experiment |
| Global parameter root count | Exclusion of additional roots across all claimed phase widths/backgrounds, not a finite scan |
| Optimal testing and design | Bounds for the exact observation/risk criterion and certified exclusion of competing designs; pooled bins do not automatically bound full counts |
| Historical priority | [Claim-level comparison](priority.md) against the outstanding primary texts, with exact hypotheses and conclusions |
| Physical validation | The [measurement protocol](../evidence/homometric-photon-counts/science_frontier/review_and_experiment/external_review_and_physical_test.txt), measured bounds supporting a [model-error budget](model-tolerance.md), and feasible acquisition analysis; no detector data are present |
| Broader formal portability | A separately validated Linux/macOS toolchain and dependency build; the supplied replay targets the retained pinned Windows environment |

The current reference four-root count is settled within its analytic/computational assumptions. The [quantitative stability proof](root-stability.md) now supplies an explicit full rectangle, controlling zero and infinite gain as well as the intervals between roots. Its exact rational budget and the fixed-bin necessary count narrow separate gaps. The formal sources now cover concrete phase harmonics, Gaussian expectations, an all-order intensity-moment formula, a proved site-by-site recurrence, and the Gaussian/Poisson marginal count-law construction. The [concrete exact certificates](../formal/CERTIFICATES.md) now close the moment-evaluation gap and prove count-law distinction for the explicit model. The [joint snapshot model](../formal/JOINT_MODEL.md) also closes the conditional Poisson interpretation; a temporal or exposure-integrated physical model remains a separate extension. Repository polish, licensing, CI, and artifact integrity support inspection but cannot replace missing mathematical or experimental evidence.
