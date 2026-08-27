---
rg: 2
id: recursive-twisted-higman-proof
kind: route
title: Centralize the recursive relator kernel, apply Thom, and Higman embed
target: recursive-twisted-factor-higman-compiler
requires:
  - thom-central-corner-criterion
  - higman-bypass-needs-only-fg-recursive-nonhyperlinear
---

Choose the canonical projective regular unitaries `(u_g)_(g in Gamma)` in
`L_omega(Gamma)`, so `u_g u_h=omega(g,h)u_(gh)`.  Composing `F -> Gamma`
with `g -> [u_g]` gives a homomorphism from `F` to the projective unitary
group.  Choose unitary lifts.  Every `n in N` is then represented by a scalar
`chi(n)I`.  Scalarity gives

```text
chi(nm)=chi(n)chi(m),
chi(f n f^-1)=chi(n),
```

so `chi` kills `[F,N]` and defines a character of the central kernel
`N/[F,N]` in

```text
1 -> N/[F,N] -> F/[F,N] -> Gamma -> 1.                 (RTH2)
```

The character sector of `(RTH2)` belonging to `chi` is the original
projective regular representation, hence its twisted von Neumann algebra is
`L_omega(Gamma)` (up to the harmless coboundary determined by the chosen
lifts).  It is non-CE.  Thom's all-character criterion therefore makes
`E=F/[F,N]` nonhyperlinear.

For effectivity, centralizing each recursively enumerated normal generator
`r in R` centralizes all its conjugates and products, hence the presentation
`(RTH1)` presents exactly `F/[F,N]`.  It has finitely many generators and an
r.e. relator set.  The established Higman bypass embeds `E` into a finitely
presented group, which remains nonhyperlinear because hyperlinearity passes
to subgroups.

