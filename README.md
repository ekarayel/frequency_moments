# Frequency Moments

[Isabelle](https://isabelle.in.tum.de/) is an interactive theorem prover, which can be used to verify mathematical theorems or the correctness of algorithms, protocols or hardware. This repository contains the formal verification of randomized, approximate space-efficient streaming algorithms for frequency moments with Isabelle/HOL.

Frequency moments can for example be used to determine the number of distinct elements, the skew of the rank-size distribution of the data stream and several statistical dispersion measures.

The source files are in the [thys folder](thys/).

The printable version of the formally verified results are available in two versions:
* [Full document](output/document.pdf?raw=1) (including proofs)
* [Outline document](output/outline.pdf?raw=1) (without proofs)

Summary of verified algorithms:
* Approximation of F_0 with space complexity: O( ln(1/ε) (ln n + 1/δ² (ln (1/δ) + ln ln n)))
* Approximation of F_2 with space complexity: O( ln(1/ε) (1/δ²) (ln n + ln m))
* Approximation of F_k for k >= 3 with space complexity: O( ln(1/ε) (1/δ²) (ln n + ln m) k n^(1-1/k))

where
* n is the size of the universe of the stream elments,
* m is the length of the stream,
* δ is the required relative accuracy (0 < δ < 1),
* ε is the maximum failure probability (0 < ε < 1).
 
## Verification

If the following is available and set up:
* [Isabelle 2021-1 Release (December 2021)](https://isabelle.in.tum.de/website-Isabelle2021-1/index.html)
* [AFP 2022-01-06 Release](https://www.isa-afp.org/release/afp-2022-01-06.tar.gz) (or newer)
* 32 GB of RAM available

```
# Clone this repo
git clone https://github.com/ekarayel/frequency_moments.git

# Plain Verification (requires 30 min)
isabelle build -D frequency_moments/thys/
```

A guide for verification if Isabelle is not pre-installed is available [here](install-and-verify.md).
