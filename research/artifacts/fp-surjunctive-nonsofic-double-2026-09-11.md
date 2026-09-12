# A finitely presented surjunctive nonsofic group

Date: 2026-09-11. Lane: `group_frontiers`.

This strengthens the existing finitely generated separation example by
checking finite presentation of a specific double. Surjunctivity uses the
new [graph-of-groups theorem](surjunctivity-graph-folds-2026-09-11.md),
whose local automaton argument is explicitly credited there to the earlier
shared peeling artifacts. Nonsoficity is the cited Kun--Thom input.

## Fixed witness

Put

```text
R_plus = F_2[x_1,x_2,x_3],
R      = F_2[x_1^+-1,x_2^+-1,x_3^+-1],
Gamma  = EL_6(R_plus),
G      = EL_6(R) semidirect SL_3(Z),
D      = G *_Gamma G.
```

The action of `SL_3(Z)` is by monomial substitutions on `R`; `Gamma`
embeds in the elementary normal factor of `G`. For definiteness, the
action sends the monomial with exponent column `v` to that with exponent
column `Mv` for `M in SL_3(Z)`.

**Theorem.** The group `D` is finitely presented, surjunctive, and nonsofic.

The only additional finite-presentation issue is the kernel between the
Steinberg group and its elementary image. It is controlled below; finite
presentation is not passed through an arbitrary quotient.

## 1. A finite kernel relation packet for the Laurent elementary group

The ring `R` is commutative regular noetherian of Krull dimension three.
It has a finite unital ring presentation: start with six symbols
`x_i,y_i`, impose characteristic two, impose pairwise commutation, and
impose `x_i y_i=1` for `1<=i<=3`.

The finite-presentation theorem for Steinberg groups therefore gives
finite presentation of `St_6(R)`. The source and rank are pinned in
Section 5 below.

Classical stability identifies

```text
ker(St_6(R) -> EL_6(R)) = K2(6,R) ~= K2(R),              (1.1)
```

because `6 = dim(R)+3`.

For `R_j=F_2[x_1^+-1,...,x_j^+-1]`, regularity and the fundamental
theorem give the recurrences

```text
K0(R_j) ~= K0(R_(j-1)),
K1(R_j) ~= K1(R_(j-1)) (+) K0(R_(j-1)),
K2(R_j) ~= K2(R_(j-1)) (+) K1(R_(j-1)).                (1.2)
```

Starting from `K0(F_2)=Z`, `K1(F_2)=1`, and `K2(F_2)=0`, this yields

```text
K0(R_j)=Z,    K1(R_j)~=Z^j,    K2(R_j)~=Z^(j choose 2).
```

In particular `K2(R)=Z^3`. Its generators can be taken to be the
three Laurent symbols `{x_1,x_2}`, `{x_1,x_3}`, `{x_2,x_3}`, by the
successive boundary splittings. Thus the whole kernel in (1.1) is
generated as a group by three elements. Its normal closure is then also
the whole kernel. Adding three relators to a finite presentation of
`St_6(R)` gives a finite presentation of `EL_6(R)`.

No unstable remainder is discarded: (1.1) is exactly why rank six was
chosen. The earlier repository three-symbol computation with only two
inverted variables is not being substituted for the three-variable
calculation (1.2).

## 2. The actor and edge group

The group `SL_3(Z)` is finitely presented. A semidirect product of two
finitely presented groups is finitely presented: take the two finite
presentations and add one conjugation relation for each ordered pair
consisting of a quotient generator and a kernel generator. The actual
action provides the finite words on the right-hand sides. The resulting
normal form is exactly the semidirect product. Hence `G` is finitely
presented.

The subgroup `Gamma` is finitely generated. More explicitly, take

```text
e_ij(1), e_ij(x_1), e_ij(x_2), e_ij(x_3),    1<=i!=j<=6.
```

These finitely many matrices generate all elementary matrices over
`R_plus`. Additivity gives
`e_ij(a+b)=e_ij(a)e_ij(b)`, while, choosing an index `k` distinct from
`i,j`, the identity

```text
[e_ik(a),e_kj(b)] = e_ij(ab)
```

produces successively every monomial and polynomial coefficient.

Finite presentation of `Gamma` is not needed.

## 3. A finite presentation of the double

Take a finite presentation `<S | T>` of `G` and a finite generating
set `c_1,...,c_m` for `Gamma`, expressed as words in `S`. With `S'`
a disjoint copied generating set, the presentation

```text
<S,S' | T(S), T(S'), c_i(S)=c_i(S') for 1<=i<=m>        (3.1)
```

defines `G *_Gamma G`. The finitely many equalities identify the
generators of the actual embedded subgroup, and therefore all its
elements; the universal property of the amalgam identifies (3.1) with
`D`. This proves finite presentation without requiring a finite
presentation of the edge group.

## 4. Surjunctivity and nonsoficity

Kun--Thom Theorem E, with `q=2`, `r=6`, and `d=3`, states that `Gamma`
and `G` are residually finite Kazhdan groups and that `Gamma` is
infranormal but not normal in `G`.

Since `G` is residually finite it is surjunctive. The fold `D->G` is
identity on both vertex groups. The graph-of-groups theorem therefore
makes `D` surjunctive. Equivalently, this is the double case of the
earlier finitary split-extension argument.

Kun--Thom Theorem A, version 3, proves that the same double `D` is
nonsofic. The nonsoficity and surjunctivity statements concern this one
fixed group, and Sections 1--3 prove that it is finitely presented.

Consequently the question whether surjunctivity characterizes soficity
has a negative answer already among finitely presented groups.
This does not settle the universal Gottschalk conjecture. No claim is
made that `D` is simple, hyperlinear, or nonhyperlinear.

## 5. Source and novelty audit

All sources below were checked on 2026-09-11. The finite-presentation
and stability chain was independently reviewed by the parallel
`quantum_complexity` agent.

* [Kun--Thom, arXiv:2608.06222v3](https://arxiv.org/html/2608.06222v3),
  Theorems A and E, supplies the pair and the double's nonsoficity.
  The current record remains v3, 20 August 2026. This is a preprint
  input, credited as such.
* [Weibel, The K-book](https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.pdf),
  Remark III.5.5.2, gives `K2(n,R)=K2(R)` for a noetherian ring of
  dimension `d` and `n>=d+3`. Theorem V.6.3 gives the regular Laurent
  splitting in (1.2); III.6.1.1 gives `K2(F_2)=0`.
  These sources justify the whole finite-rank kernel, not merely its
  stable image.
* [Ershov--Jaikin-Zapirain](https://arxiv.org/pdf/0809.4095v2), Section
  6.1, printed page 35, explicitly states the Krstic--McCool theorem:
  `St_n(R)` is finitely presented for a finitely presented ring and
  `n>=4`. A second source is
  [Allcock, Steinberg groups as amalgams](https://msp.org/ant/2016/10-8/ant-v10-n8-p05-p.pdf),
  Theorem 12.1, printed page 1837, recording Splitthoff's theorem for
  commutative finitely generated rings and root rank at least three.
* [Sakasai, Algebraic & Geometric Topology 12 (2012)](https://msp.org/agt/2012/12-1/agt-v12-n1-p12-s.pdf),
  printed page 276, explicitly records a finite presentation of
  `SL_3(Z)` on the six elementary matrices. Printed page 280 describes
  its thirteen relators. This supplies the actor's quotient-group
  finite-presentation input independently of the Laurent-ring argument.

The K-theoretic finite-presentation calculation is standard. The new
consequence in this batch combines it with the surjunctivity proof,
and is distinct from the earlier finitely generated wreath witness.
Repository searches found no earlier claim of a finitely presented
surjunctive nonsofic group. No claim of exhaustive bibliographic novelty,
Lean certification of the mathematical argument, or computational
exhaustion is made.
