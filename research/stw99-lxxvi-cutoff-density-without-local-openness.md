---
rg: 2
id: stw99-lxxvi-cutoff-density-without-local-openness
kind: claim
title: Positive cutoff restriction has dense image in stable rank one but need not be locally open even after closure
distinct_from:
  stw99-lxxvi-exact-positive-cutoff-restriction-not-onto: This proves density and a quantitative failure of local approximation near a prescribed larger frame, rather than merely failure of exact surjectivity.
artifacts:
  - research/artifacts/stw99-lxxvi-dense-cutoff-restriction-and-local-control-2026-09-05.md
---

Let B be a C*-algebra, d in B_+ with Her(d) of stable rank one,
a in B_+, and b=(a-eta)_+ for eta>0. Define

```text
F(a,d)={w in closure(dB):w*w=a},
h(t)=sqrt((t-eta)_+/t) for t>0, h(0)=0.
```

If F(a,d) is nonempty, the actual restriction map

```text
rho:F(a,d)->F(b,d),       rho(w)=w h(a)
```

has norm-dense image. This is a consequence of CEI's prior-art
approximate unitary equivalence of Hilbert-module embeddings; the
artifact supplies a direct estimate. If B has stable rank one,
[a]<=[d] ensures the required nonemptiness. Hereditary K-stability,
strict comparison, and real rank zero are not needed for density.

However, in the CAR algebra there are such a,b with [a]<[1], a
frame w_0 in F(a,1), and an exactly liftable continuous family
v_t in F(b,1) converging to rho(w_0), for which

```text
||rho(w)-v_t|| <= sqrt(t)/2  implies  ||w-w_0|| >= 3/4.
```

Consequently, for every r<3/4, the closure of the image under rho
of the source r-ball about w_0 contains no neighborhood of rho(w_0).
This holds despite global density, even for a coefficient with real
rank zero and K-stable hereditary subalgebras throughout its stabilization.

The result does not rule out parameterized approximation with fixed
uniform error or iterations that change cutoff levels. It supplies
no counterexample to general LXXVI. The proof is internally reviewed.

ROUTES

stw99-lxxvi-cutoff-density-local-control-proof
