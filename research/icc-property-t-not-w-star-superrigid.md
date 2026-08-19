---
rg: 2
id: icc-property-t-not-w-star-superrigid
kind: claim
title: ICC property (T) groups need not be W-star superrigid
artifacts:
  - research/artifacts/connes-rigidity-counterexample-2026-08-19.md
---

ESTABLISHED.

There are countable discrete groups `Gamma_1` and `Gamma_2` such that

```text
both are ICC,  both have property (T),  Gamma_1 !~ Gamma_2,
and                 L(Gamma_1) ~ L(Gamma_2).
```

Connes' rigidity conjecture for ICC property (T) groups — every such group is
recoverable from its group von Neumann algebra — is therefore false.  The
conjecture for higher rank lattices, which is the geometric statement Mostow
and Margulis motivate, is untouched and remains open.

## The construction

Shuoxing Zhou (ENS), *ICC Property (T) Groups without W\*-Superrigidity*,
manuscript read 2026-08-19; obtained with assistance from GPT-5.6 Sol,
independently of and concurrently with an OpenAI Astra construction announced
2026-08-01, cited there as chapter 4 of the same release whose nonsoficity
chapter this graph imports at `openai-leavitt-unit-nonsofic`.

```text
k = F_2,  R = k[t],  A = R^3,  C = (A tensor A)^Flip,  V = k^4 symplectic
Q = Sp_4(k) finite,  H = SL_3(R) x Q,  D = (A tensor V^*) + C
theta_1(l,q)(u,c) = ((l,q).u,                          l.c)
theta_2(l,q)(u,c) = ((l,q).u + l delta(c) tensor ell_q, l.c)
Gamma_i = D rtimes_(theta_i) H
```

Here `delta:C -> A` is the equivariant retraction of `a |-> a tensor a` and
`ell_q = q.r_0 - r_0` is the `Sp_4(k)`-cocycle of the quadratic refinement
`r_0 = a_1b_1 + a_2b_2`; `ell` is linear in `V^*` because `q` preserves the
polarization `omega`, and it is not a coboundary.

**Same kernel, same quotient, two actions.**  Both groups are extensions of the
same `H` by the same elementary abelian `D`; only the action differs, by the
one cocycle term.  That is what makes the pair sharp: no invariant of the
constituents can separate them, and no invariant of the algebra can either.

## Why the two factors agree

Fourier transform turns each group factor into a crossed product by the dual
action, `L(Gamma_i) = L^infty(hat D_i) rtimes H`, and the quadratic **fibre
shear**

```text
F(z,y) = (z, y + calR(z)),      calR(z) = x_1 tensor x_2 + x_3 tensor x_4
```

is a Haar-preserving involutive homeomorphism of `hat D` conjugating
`alpha_1` to `alpha_2`, because the defect `J_q(z)` of the second dual action
is exactly `calR(qz) - calR(z)`.  `F` is **not** an automorphism of the compact
group `hat D` — `calR` is quadratic — so it destroys the module structure while
preserving everything the crossed product sees.

## Why the two groups differ

`D_i` is the unique largest normal elementary abelian exponent-two subgroup of
`Gamma_i`, hence characteristic, and `Q` is the unique largest finite normal
subgroup of `Gamma_i/D_i = SL_3(R) x Q`, hence characteristic there.  Any
isomorphism therefore restricts to an isomorphism of `Q`-modules
`D_1 -> beta^*D_2`.  But `D_1` is a sum of copies of the simple modules `V^*`
and `k`, while `D_2` contains the nonsplit extension `E_ell = V^* + k`, which
is nonsplit precisely because `ell` is not a coboundary.  Semisimple against
non-semisimple; pullback along `beta` preserves the distinction.

## Where this bears

- Approximation side: the consequence for this program is drawn separately at
  `hyperlinearity-cannot-see-the-lamp-module`, because hyperlinearity is a
  property of `L(Gamma)`, so it cannot distinguish `Gamma_1` from `Gamma_2`.
- Separation side: `scaling-family-pairwise-nonisomorphic` and
  `continuum-nonisomorphic-fg-non-mf` ask this graph's own version of the
  question Zhou answers — tell apart the members of an explicit family of
  similarly built groups.  The transferable part is the *method*: extract a
  characteristic normal abelian subgroup, then compare the induced module
  structures over the quotient, using a cohomological (split versus nonsplit)
  invariant when the obvious numerical ones agree.  Nothing here says the
  `E_m` have such a subgroup; that identification is exactly the work.
- Property (T) is not the rigidity engine it was assumed to be for group
  factors.  This costs the corpus nothing, since no node derives an
  approximation conclusion from W\*-rigidity, but it is worth knowing before
  anyone reaches for one.

Recorded as an external landmark, not as progress on any candidate.  It is
deliberately left with no route consuming it — the same standing as
`hyperlinear-near-representation-criterion` — and its only downstream node is
the corollary named above.
