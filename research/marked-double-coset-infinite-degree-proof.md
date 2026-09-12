---
rg: 2
id: marked-double-coset-infinite-degree-proof
kind: route
title: Cut a root subgroup against the denominator ideal
target: marked-double-coset-infinite-degree
requires: [kun-thom-nonsofic-wreath]
artifacts:
  - notes/COMMUTING_WREATH_SOFIC_RADICAL.md
---

## Direct proof

Throughout, `Gamma=EL_r(R_+)` contains the root subgroups
`U_(ij)={e_(ij)(a) : a in R_+}`, each isomorphic to the additive group of
`R_+`, and every element of `Gamma` has all entries in `R_+`.

**Denominator lemma.**  Let `0!=f in R`.  Write `f=x^w P` with `w in Z^d` and
`P in R_+` divisible by no variable; this is unique.  Then

```text
{a in R_+ : a f in R_+} = x^(w^-) R_+,
```

where `w^-_k=max(0,-w_k)`.  Indeed `a x^w P in R_+` iff
`x^(w^-)` divides `a x^(w^+) P`, and `w^+`, `w^-` have disjoint support, so
this says `x^(w^-)` divides `a P`, hence divides `a` by unique
factorization in `R_+` and coprimality of `P` to the variables.  If
`w^- != 0`, say `w^-_1>0`, then the monomials `x_2^s`, `s>=0`, lie outside
`x^(w^-)R_+` and no difference of two of them lies in it, so the additive
index of `x^(w^-)R_+` in `R_+` is infinite.  This is where `d>=2` is used.

**1. Necessary condition.**  Suppose `[Gamma : Gamma cap h Gamma h^(-1)]=n`
is finite and fix `i!=j`.  The set

```text
D_(ij) = {a in R_+ : e_(ij)(a) in h Gamma h^(-1)}
```

is a subgroup of `(R_+,+)`, since `a |-> e_(ij)(a)` is a homomorphism and
`h Gamma h^(-1)` is a group; and
`[(R_+,+) : D_(ij)] = [U_(ij) : U_(ij) cap h Gamma h^(-1)] <= n`, because the
index of an intersection with a subgroup is at most the ambient index.

For `a in D_(ij)` we have `h^(-1) e_(ij)(a) h in Gamma`, and

```text
h^(-1)(I + a E_(ij))h = I + a * h^(-1)E_(ij)h,
   (h^(-1)E_(ij)h)_(pq) = (h^(-1))_(pi) h_(jq),
```

so `a (h^(-1))_(pi) h_(jq) in R_+` for every `p,q`.  Hence `D_(ij)` is
contained in the intersection over `p,q` of the sets of the denominator
lemma.  If some `(h^(-1))_(pi)h_(jq)` were outside `R_+`, that intersection
would already have infinite additive index, contradicting
`[(R_+,+):D_(ij)] <= n`.  So all these products lie in `R_+`.

**2. The marked element.**  For `h=e_12(x^m)=I+x^m E_12` one has
`h^(-1)=I-x^m E_12`, so with `i=2`, `j=1`, `p=q=1`,

```text
(h^(-1))_(12) h_(11) = -x^m,
```

which lies outside `R_+` exactly when `m` is not in `N^d`.  The recorded
marked element has `m=-(1,...,1)`.  By 1 the index is infinite.  Since the
`Gamma`-orbit of `h Gamma` in `X=G/Gamma` has cardinality
`[Gamma : Gamma cap h Gamma h^(-1)]`, that orbit is infinite, and the
orbital graph of the double coset `Gamma h Gamma` — whose degree at `y` is
the size of the `Gamma_y`-orbit of the corresponding neighbour — has
infinite degree.

**3. Consequence.**  A `G`-invariant graph is a union of `G`-orbits of
unordered pairs.  If it contains `{Gamma, h Gamma}` it contains that whole
orbit, whose degree at the base point is already infinite by 2.  So it has
infinite degree.

**4. The fixed set.**  `y Gamma` is fixed by `Gamma` iff `y^(-1) Gamma y`
is contained in `Gamma`, i.e. iff `y^(-1)` lies in the compression
semigroup `P_Gamma`; so `X^Gamma = P_Gamma^(-1)Gamma/Gamma`.  For a strict
compressor `t`, `ray-injectivity` (formalized) says no positive power of `t`
lies in `Gamma`, so the cosets `t^(-n)Gamma` are pairwise distinct and all
lie in `X^Gamma`.

For the translate identity, `y Gamma` is fixed by `s Gamma s^(-1)` iff
`y^(-1)s Gamma s^(-1) y <= Gamma`, i.e. iff `w=s^(-1)y` satisfies
`w^(-1)Gamma w <= Gamma`, i.e. iff `w in P_Gamma^(-1)`.  Hence
`X^(s Gamma s^(-1)) = s P_Gamma^(-1)Gamma/Gamma = s * X^Gamma`.  If `t` is a
compressor and `w^(-1) in P_Gamma`, then
`(t^(-1)w)^(-1)Gamma(t^(-1)w) = w^(-1)(t Gamma t^(-1))w <= w^(-1)Gamma w <= Gamma`,
so `X^Gamma <= t X^Gamma`.  The inclusion is strict: `t Gamma in t X^Gamma`,
while `t Gamma in X^Gamma` would give `t^(-1)Gamma t <= Gamma` and hence
`t Gamma t^(-1) = Gamma`, contradicting strictness.

## Scope

This is a statement about the specific Laurent pair of Kun--Thom Theorem E
and about elementary marked elements `h=e_12(x^m)`.  Condition 1 is only
necessary, so it cannot be used to certify that some other double coset *is*
finite; it is used here only in its contrapositive.  Nothing here says the
invariant-graph family is empty — the complete graph and every other
nondegenerate invariant graph remain available, all of infinite degree.
