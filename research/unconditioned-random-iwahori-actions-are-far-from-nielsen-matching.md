---
rg: 2
id: unconditioned-random-iwahori-actions-are-far-from-nielsen-matching
kind: claim
title: Independent random Iwahori actions stay a constant distance from every Nielsen matching
artifacts:
  - research/artifacts/dyadic-random-dessin-entropy-firewall-2026-08-22.md
distinct_from:
  dyadic-amplified-edge-random-lifts-exist: that asks for specially correlated edge restrictions which also extend to the two modular vertices; this rules out the unconditioned random-edge ansatz and does not count the rare extendible locus.
  dyadic-radial-shell-couplings-have-one-third-boundary: that is a deterministic weighted-boundary obstruction for geometric sphere mixtures; this is an entropy obstruction for random labelled Iwahori Schreier graphs.
---

Let `B=<u,e | e^2=1> ~= Z*C_2` and let

```text
alpha(u)=u^(-1)e,        alpha(e)=u^(-1)e u.
```

For even `n`, independently sample two homomorphisms
`sigma_i:B->Sym(n)` by taking `sigma_i(u)` uniformly in `Sym(n)` and
`sigma_i(e)` uniformly among fixed-point-free involutions.  For every fixed
`epsilon<1/4`, with probability tending to one there is no permutation
`S in Sym(n)` such that

```text
d_H(S sigma_0(u) S^(-1), sigma_1(alpha(u))) <= epsilon,
d_H(S sigma_0(e) S^(-1), sigma_1(alpha(e))) <= epsilon.
```

Thus an unconditioned random high-girth `Z*C_2` Schreier graph and an
independent Nielsen-twisted one do not provide the edge near-conjugacy in
the dyadic random-lift program.  A successful dessin construction must
correlate the two restrictions before randomizing their modular orbit
incidence; generic edge actions are exponentially too far apart.

