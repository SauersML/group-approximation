# Independent review: HS stability of Kazhdan hyperbolic groups

Reviewer lane `reviewer`, 2026-09-12. This is an adversarial review of the claims that convert Hilbert–Schmidt stability of a Kazhdan hyperbolic group into a non-hyperlinear hyperbolic group, or into a persistent degree-two class:

- `kazhdan-hyperbolic-hs-stability-kills-hyperlinearity` and `kazhdan-hyperbolic-hs-stability-kills-hyperlinearity-proof`;
- `hs-stable-hyperlinear-kazhdan-hyperbolic-forces-persistent-class` and `hs-stable-hyperlinear-kazhdan-hyperbolic-persistent-class-proof`;
- the inputs:
  - `hs-stability-forces-nonhyperlinear-central-extension` (Dogon–Vigdorovich import);
  - `hyperlinear-flexibly-hs-stable-group-is-residually-finite`;
  - `finite-kernel-nonrf-has-central-prime-reduction`;
  - `finite-central-extension-rf-iff-virtually-splits`.

## Verdicts

| claim | verdict | trust surface |
| --- | --- | --- |
| `kazhdan-hyperbolic-hs-stability-kills-hyperlinearity` | **PASS** | Dogon–Vigdorovich main theorem (arXiv:2506.20843v2) |
| `hs-stability-forces-nonhyperlinear-central-extension` | **PASS**, numbering corrected | statement matches the v2 PDF verbatim, where it is **Theorem 1.3**; the node said Theorem 1.1 |
| `hs-stable-hyperlinear-kazhdan-hyperbolic-forces-persistent-class` | **PASS** | inherits Dogon–Vigdorovich |
| `hyperlinear-flexibly-hs-stable-group-is-residually-finite` | **PASS** | none (Malcev) |
| `finite-kernel-nonrf-has-central-prime-reduction` | **PASS** | none |
| `finite-central-extension-rf-iff-virtually-splits` | **PASS** | none (folklore, proof checked) |

**Bottom line.** Flexible HS stability of one hyperbolic Kazhdan group with `b_2 >= 1` would give a non-hyperlinear hyperbolic group, which is nonsofic and not residually finite. If that group is also hyperlinear, the same premise forces a persistent prime class in `H^2` of a finite-index subgroup, so the group is not good. Every step checks. The notion of stability matches the source: Dogon–Vigdorovich define "Hilbert–Schmidt stable" as the flexible notion (`D_n >= d_n`), and they call `D_n = d_n` "strictly Hilbert–Schmidt stable". So the premise these claims need is the weaker, flexible one, consistent with Becker–Lubotzky's exclusion of strict stability for infinite hyperlinear Kazhdan groups.
