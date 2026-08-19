---
rg: 2
id: exact-support-relator-sparsification-proof
kind: route
title: Competing finite union bounds produce the marked nonhyperlinear presentation
target: exact-support-relator-sparsification
requires:
  - finite-trace-profile-net-is-dimension-free
artifacts:
  - research/artifacts/lcs-exact-support-sparsification-2026-08-18.md
---

Choose a profile-net radius `eta` with

```text
2 eta < eps_plus^2-eps^2
```

and let `N` be the finite net size of the compact `delta`-marked profile space.
Because `g>q`, choose `m` large enough that

```text
g^m > N q^m.
```

Sample `m` relators independently from `mu`.

With probability exactly `g^m`, every sampled relator lies in `E`.  On that
event the tracial assignment `rho` satisfies the sampled presentation exactly,
while `rho(j)` stays a fixed positive 2-distance from `1`; hence `j` is
nontrivial in the sampled group.

For one net profile, the chance all sampled relators are `eps_plus`-small is at
most `q^m`.  The union bound over the `N` profiles is at most `Nq^m`.  If an
actual finite-dimensional `delta`-marked tuple satisfied all sampled relators
to defect `eps`, its `eta`-near profile would satisfy all of them to defect
`eps_plus`, by

```text
2-2z_r <= (2-2x_r)+2 eta < eps_plus^2.
```

Thus the probability that any such tuple exists is at most `Nq^m`.

Since `g^m>Nq^m`, some sampled multiset lies in the first event but not the
second.  For its presentation, there is an exact tracial representation with
`j` nontrivial, but there is one positive relator tolerance for which no
finite-dimensional approximate representation keeps `j` `delta`-separated.
By the standard definition of nontriviality in approximate representations,
`j` is therefore trivial in approximate representations.  A hyperlinear group
cannot contain such a nontrivial element, so the sampled finitely presented
group is nonhyperlinear.
