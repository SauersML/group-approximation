---
rg: 2
id: stw84-partial-shifts-and-the-fixed-implementer-gate-proof
kind: route
title: Extend finite partial translations, test the implementer itself, and isolate the fixed-implementer gate
target: stw84-alternating-shift-approximate-representability-gate
requires:
  - stw84-invariant-coefficient-stages-restore-two-fourier-colours
artifacts:
  - research/artifacts/stw84-alternating-shift-coherence-audit-2026-08-30.md
---

## 1. Exact implementation on an arbitrary coefficient packet

Fix finite `F subset B` and `epsilon>0`.  Since the group algebra is dense,
there is a finite set `S subset Z` such that every member of `F` is within
`epsilon` of `C*(Alt(S))`.  Enlarge `S` if necessary so that `|S|>=3`.

The injection `j |-> j+1` from `S` to `S+1` extends to a finitary
permutation `p` of `Z`.  If its parity is odd, multiply it on the left by a
transposition supported on two fresh points outside `S+1`; this changes
neither `p(j)=j+1` for `j in S` nor the conjugation it induces on
`Alt(S)`.  Thus `p in Alt_fin(Z)` and

```text
p g p^(-1)=s g s^(-1)                 (g in Alt(S)).  (APS1)
```

Put

```text
H=Alt(S), E=C*(H), L=<H,p>, D=C*(L), v=lambda_p.
```

The group `L` is finite because `K` is locally finite.  Hence `E subset D`
are finite dimensional, `v in U(D)`, and `(APS1)` gives `(ASC1)` on all of
`E`, not merely on the selected approximants.

Notice the quantifier defect: `v` lies in `D`, but `(ASC1)` controls only
the smaller coefficient algebra `E`.  Enlarging the controlled algebra to
`D` forces one to test the estimate on `v` itself.

## 2. Every group implementer has a uniform invariance gap

If `p in K` and `alpha(p)=p`, then the finite support of `p` is invariant
under translation by one.  The only finite translation-invariant subset of
`Z` is empty, so `p=1`.  Therefore `q=p^(-1)alpha(p)` is nontrivial whenever
`p` is nontrivial.

The regular representation is faithful because `K` is amenable, and

```text
||alpha(lambda_p)-lambda_p||=||lambda_q-1||.          (APS2)
```

Let `m>=2` be the order of `q`.  On every left coset of `<q>`, `lambda_q`
is the cyclic permutation of length `m`; its spectrum contains all
`m`-th roots of unity.  Hence

```text
||lambda_q-1||
 = max_(0<=j<m)|exp(2 pi i j/m)-1|
 = 2                         if m is even,
 = 2 cos(pi/(2m))            if m is odd.
```

For odd `m>=3` the last expression is at least `sqrt(3)`.  This proves
`(ASC2)`.  In particular the exact partial translations from Section 1
cannot even begin to satisfy whole-stage coherence below that universal
threshold.

This argument is intentionally limited to group unitaries.  An arbitrary
unitary of a finite group algebra is not a group basis element, so `(APS2)`
does not give a lower bound for it.

## 3. Coherent stages imply approximate representability

Let `F subset B` be finite and let `epsilon>0`.  Apply coherent innerness
with `delta<epsilon/3`, obtaining `D` and `v in U(D)`.  For each `a in F`
choose `d_a in D` with `||a-d_a||<delta`.  Uniform near-innerness on `D_1`
gives

```text
||alpha(a)-v a v^*||
 <= ||alpha(a-d_a)||
    +||alpha(d_a)-v d_a v^*||
    +||v(d_a-a)v^*||
 <3 delta<epsilon.                                      (APS3)
```

Taking `d=v` in the same uniform estimate gives

```text
||alpha(v)-v||=||alpha(v)-v v v^*||<delta<epsilon.       (APS4)
```

Equations `(APS3)--(APS4)` are approximate representability for a unital
automorphism.  The standard duality identifies this with the Rokhlin
property of the dual circle action on `B rtimes_alpha Z`.  No converse to
the coherent-stage condition is asserted.

## 4. Why a prescribed finite set cannot replace the unit ball

The failure is already finite dimensional.  Take

```text
D=M_2 tensor M_2,       E=M_2 tensor 1,
W=1 tensor diag(1,-1).
```

Then `W` commutes with every element of `E`, hence with any prescribed
finite coefficient packet in `E`, but

```text
D'=C1,                  dist(W,D')=1.                  (APS5)
```

Indeed the spectrum of `W` is `{1,-1}`, so its distance from the scalars is
one.  Haar averaging over `U(D)` sends `W` to its normalized trace, namely
zero, and moves it by norm one.  Thus exact covariance on the coefficient
packet supplies no perturbative access to the commutant of the containing
stage.

There is one precise positive version.  If `S subset D_1` is an `eta`-net
and

```text
max_(s in S)||W s W^*-s||<=kappa,
```

then for every `d in D_1`, choosing `s in S` with `||d-s||<eta` gives

```text
||W d W^*-d||<=kappa+2 eta.                            (APS6)
```

Therefore a finite set chosen after the stage and norming its whole unit
ball is sufficient.  Its quantifiers are simply the whole-stage hypothesis
used in the Haar proof.  The exact local implementation from Section 1,
where the controlled algebra is proper and does not contain `v`, does not
meet it.
