---
rg: 2
id: exact-codensity-does-not-imply-matricial-rcc
kind: claim
title: Exact finite-dimensional co-density does not imply matricial relative-commutant collapse
artifacts:
  - research/artifacts/sl3-projective-rcc-audit-2026-08-21.md
distinct_from:
  exact-projective-codensity-has-a-uniform-trace-square-gap: that is an exact finite-dimensional theorem; this shows that even its strongest image-equality hypothesis has no automatic tracial-ultraproduct extension.
  coset-bernoulli-ce-refutes-relative-commutant-collapse: that conditionally refutes a specific arithmetic RCC pair via a CE action; this gives an unconditional non-arithmetic countermodel to the abstract implication.
  projective-transfer-equals-rcc-for-perfect-pairs: that identifies projective and ordinary transfer once a qualitative ultraproduct theorem is available; this shows exact finite-dimensional co-density cannot supply that theorem by itself.
---

There is a finitely generated perfect Kazhdan group `C` inside a countable
perfect hyperlinear group `A` such that every finite-dimensional unitary
representation `rho` of `A` satisfies

```text
rho(A)=rho(C),
```

but relative-commutant collapse fails maximally in the canonical regular
tracial model of `A`.

Take

```text
C = SL_3(Z),       D = A_fin,       A = C x D,
```

where `A_fin` is the finitary alternating group on a countable set. Every
finite-dimensional unitary representation of the infinite simple locally
finite group `D` is trivial. Hence exact finite-dimensional image equality
holds. Nevertheless, for noncommuting `x,y in D`, the regular-model unitary
`u=1 tensor lambda_D(x)` commutes with `C`, whereas for `h=(1,y)`,

```text
[u,lambda_A(h)] = 1 tensor lambda_D([x,y])
```

has trace zero. In particular its projective trace-square energy is one.

Thus exact co-density, perfectness, and property (T) of the subgroup do not
control approximate/tracial-ultraproduct relative commutants. A proof for
the arithmetic `SL_3` pair must use arithmetic coupling absent from a direct
product, not only equality of exact finite-dimensional images.

## A finitely presented stable-base counterexample

There is also an elementary finitely presented version which shows exactly
why the spectral gap on the co-dense subgroup is indispensable.  Put

```text
G=<r,a,k | r a r^(-1)=a^2, [k,a]=1>,
w=[k,r^(-1) a r].                                      (ECD1)
```

Thus `G` is the HNN extension of `BS(1,2)` obtained by centralizing `<a>`.
The element `r^(-1)ar` is a square root of `a` and is not in `<a>`, so
Britton's lemma gives `w!=1`.

Nevertheless every finite-dimensional unitary representation of `G` kills
`w`.  Indeed, let `R,A` satisfy `RAR^(-1)=A^2`, and let `Omega` be the finite
spectrum of `A`.  Squaring preserves spectral multiplicities and is therefore
a permutation of `Omega`.  If `B=R^(-1)AR`, then `B^2=A` and
`spec(B)=Omega`.  On the `lambda`-eigenspace of `A`, the spectrum of `B` is
contained in

```text
{mu in Omega: mu^2=lambda},
```

which is a singleton because squaring permutes `Omega`.  Hence `B` is a
function of `A`, so every operator commuting with `A` also commutes with
`B`.  In particular the relation `[k,a]=1` forces `w=1` in every exact
finite-dimensional representation.

This exact collapse has no normalized-HS modulus.  For any odd `q`, set
`zeta=exp(2 pi i/q)` and `h=(q+1)/2`, and on the basis `(e_j)_(j in Z/qZ)`
define

```text
A_q e_j=zeta^j e_j,
R_q e_j=e_(h j),
K_q e_j=e_(j+1).                                      (ECD2)
```

Then the Baumslag--Solitar relation is exact,

```text
R_q A_q R_q^(-1)=A_q^2,
```

while

```text
||[K_q,A_q]-1||_2=|zeta-1| -> 0.                      (ECD3)
```

On the other hand `B_q=R_q^(-1)A_qR_q` is diagonal with eigenvalues
`zeta^(h j)`, and therefore

```text
||[K_q,B_q]-1||_2=|zeta^h-1| -> 2.                    (ECD4)
```

So `(R_q,A_q,K_q)` are approximate representations of the fixed
three-generator presentation with vanishing defect and asymptotically
maximal marked defect.  The group `G` is itself hyperlinear by
`amenable-edge-hnn-preserves-hyperlinearity`; its base `BS(1,2)` is an
amenable HS-stable group.  Thus flexible stability of the base plus exact
finite-dimensional collapse along the dyadic root subgroup is still
insufficient.  The `(T;FD)`/`(tau)` projection in
`hnn-over-codense-kazhdan-subgroup-not-hyperlinear` is not a technical
convenience: without its uniform commutant gap, adjacent eigenvalues of `A_q`
become nearly indistinguishable while their canonical dyadic square roots
are nearly opposite.
