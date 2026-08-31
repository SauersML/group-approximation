---
rg: 2
id: link-threshold-phase-frustration-proof
kind: route
title: Count interval crossings and regroup triangle parity by half-edges
target: link-thresholds-need-macroscopic-phase-frustration
requires:
  - diagonal-parity-is-hecke-but-tau-misses-local-links
  - proper-torus-diagonal-code-is-incomplete-cover-curl
---

The order and cardinality statements in (LTF1)-(LTF2) follow from the
link-firewall proof and the subgroup orders

```text
|H|=2n,      |N|=4n,       |P|=2mn.
```

The edge graph has degree `[P:H]=m`, so the edge count is also the
handshake identity `2|E|=m|V|`.

We first count the interval boundary. Write `m=2L+1`, so the interval in
(LTF3) has length `L=(m-1)/2`. For a nonzero cyclic step whose least
absolute residue is `ell<=L`, the multiset of edges

```text
{ {z,z+s}:z in Z/mZ }
```

crosses the interval boundary exactly `2ell` times. This follows by
looking at the `ell` starting points immediately before each of the two
ends of the interval.

For the first connection orbit, the least absolute residues are

```text
4^j,       0<=j<n,
```

and their sum is

```text
sum_(j=0)^(n-1)4^j=(4^n-1)/3=m/3.                      (LTP1)
```

For the second orbit, the modular half of `1` has least absolute residue
`L`, while for `j>=1` the modular half of `4^j` is the ordinary integer
`2*4^(j-1)`. Their sum is

```text
L+sum_(j=1)^(n-1)2*4^(j-1)
 =(m-1)/2+(m-3)/6.                                      (LTP2)
```

Adding (LTP1) and (LTP2) gives `m-1`. The projective torus element
`h(2)` has order `2n`: its conjugation action on `U` has period `n`,
so every displayed connection step occurs twice. Multiplying by the two
crossings per least residue and by this central-sign multiplicity proves
`|partial_link I|=4(m-1)`. Translation of the interval is an automorphism
of the circulant link and preserves this count.

Now fix one vertex `v`. A selected triangular face containing `v`
corresponds to one edge of `link(v)`. The star cochain `s_(v,S)` is zero
on the edge opposite `v`, so its face parity is one exactly when the two
incident star edges have different membership in `S`. This proves (LTF5).

The one-cochain supported on the entire star of `v` is
`delta_0(1_v)`. Hence either compare `s_(v,S)` with zero, changing `|S|`
edges, or compare it with that full-star coboundary, changing `m-|S|`
edges. Both comparison cochains lie in `B^1`, which is contained in
`Z^1`; division by `|E|` proves (LTF6).

For a family of half-edge functions, addition of all star cochains gives

```text
sum_v s_(v,I_v)({u,v})
 =eta_u({u,v})+eta_v({u,v}),
```

which is (LTF7). Around a triangle, each vertex contributes exactly its
two incident half-edge bits. Regrouping the six bits by vertices proves
the identity (LTF8). The support of a sum of binary functions is contained
in the union of their supports. Equations (LTF4) and (LTF8) therefore give
(LTF9). Since `|G|=|V||P|=2|V|mn`, division proves (LTF10).

Finally let `R` be a set of vertices and let `c` be the sum of their
threshold star cochains. For each `v in R`, choose either zero or the
full-star coboundary according to the nearer of `I_v` and its complement.
The sum of these choices is again a coboundary. By the Hamming triangle
inequality, at most

```text
|R|(m-1)/2
```

edges must be changed. Using `|E|=m|V|/2` gives

```text
dist_E(c,Z^1)
 <=|R|(m-1)/(m|V|)
 <|R|/|V|,
```

which is (LTF12). This also explains why the all-vertex construction is
the first density at which the local distance upper bound stops
vanishing. No lower bound on (LTF11) was used or obtained.
