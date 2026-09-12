# Residual finiteness and virtual torsion-freeness: full Osin reduction

Checked 2026-09-11. This artifact supports
`hyperbolic-rf-question-equals-vtf-question-proof`. The equivalence is proved;
the existence of either counterexample is not asserted. This is an ordinary
mathematical proof using explicitly cited geometric group theory theorems,
not a Lean formalization or a construction of a new group.

## Statement and notation

For any group `G`, let

```text
R_f(G) = intersection {ker(phi) : phi:G -> F, F a finite group}.
```

Then `G` is residually finite if and only if `R_f(G)={1}`. The following
existential statements are equivalent:

1. A word-hyperbolic group `G` has `R_f(G) != {1}`.
2. A word-hyperbolic group has no torsion-free subgroup of finite index.

The groups witnessing the two assertions can differ. More precisely, from
`1 != g in R_f(G)` of infinite order we produce an integer `k>=1` such that,
for every sufficiently large positive integer `j`, the group

```text
Q_j = G / normal_closure_G(g^(kj))
```

is word-hyperbolic and the image of `g` has exact order `kj>1` and belongs
to `R_f(Q_j)`. This is the required torsion obstruction.

## Elementary finite-quotient facts

For every finite-index subgroup `H<=G`, the action of `G` on the finite set
`G/H` gives a homomorphism to a finite symmetric group with kernel

```text
core_G(H) = intersection_(a in G) a H a^(-1) <= H.
```

Consequently `R_f(G)<=H`. In particular, if `R_f(G)` contains nonidentity
torsion, every finite-index subgroup contains that torsion and `G` is not
virtually torsion-free. This fact does not need hyperbolicity.

If `pi:G->Q` is a quotient homomorphism, then

```text
pi(R_f(G)) <= R_f(Q).
```

Indeed any homomorphism `psi:Q->F` with finite target composes with `pi` to
a homomorphism from `G` to a finite group. Thus it kills `pi(g)` whenever
`g in R_f(G)`. This is an inclusion; no equality or residual-finiteness
preservation under arbitrary quotients is being asserted.

Finally, suppose every finite subgroup of `G` is conjugate into one of the
finite groups `F_1,...,F_r<=G`. If `R_f(G)` is torsion-free, it misses the
finite set `T=union_i(F_i minus {1})`. For each `t in T`, choose
`phi_t:G->A_t` to a finite group with `phi_t(t)!=1`; this is exactly what
`t notin R_f(G)` means. The diagonal map to `product_t A_t` has normal,
finite-index kernel `K` with `K intersect F_i={1}` for each `i`. A nonidentity
torsion element of `K` would be conjugate into some `F_i`, and normality would
put that conjugate in `K intersect F_i`, a contradiction. Hence `K` is
torsion-free. The empty product is allowed when `T` is empty.

Combining the preceding paragraphs proves, under the finite-carrier
hypothesis,

```text
G virtually torsion-free <=> R_f(G) torsion-free.
```

## Imported geometric inputs

Only the following geometric facts enter this proof.

- A word-hyperbolic group has finitely many conjugacy classes of finite
  subgroups. A convenient numbered reference is Wolfgang Lück,
  *Survey on geometric group theory*, arXiv:0806.3771, Theorem 7.2(v)(d).
  The statement, including the finite-subgroup clause, was checked in the
  [arXiv PDF](https://arxiv.org/pdf/0806.3771). This supplies the carrier in
  the previous section.
- For an infinite-order element `g` in a word-hyperbolic group, its maximal
  elementary subgroup `E(g)` makes `G` relatively hyperbolic with peripheral
  collection `{ {1}, E(g) }`. This is Osin, *Elementary subgroups of relatively
  hyperbolic groups and bounded generation*, Definitions 1.2 and 1.4 and
  Corollary 1.7, [arXiv:math/0404118](https://arxiv.org/pdf/math/0404118),
  pp. 3--4. Here the 2004 term “hyperbolically embedded” means adjoining
  a peripheral in an Osin relatively hyperbolic structure. `E(g)` is
  virtually cyclic, and the elementary argument in the next section shows
  `<g>` has finite index.
- Osin, *Peripheral fillings of relatively hyperbolic groups*, Theorem 1.1
  and Corollary 1.2, [arXiv:math/0510195v3](https://arxiv.org/pdf/math/0510195),
  pp. 2--3, give a finite forbidden set for peripheral normal subgroups.
  Avoiding it preserves the embeddings of the peripheral quotients and
  relative hyperbolicity of the filled group. For finitely generated `G`,
  hyperbolic peripheral quotients make the filled group word-hyperbolic;
  finite peripheral quotients suffice. These numbered statements were
  checked directly on 2026-09-11. The separate finite-set injectivity clause
  of Theorem 1.1 is not needed below.

These imported theorems are the trust boundary. The argument does not
replace their geometric proofs with computation.

## Proof of (2) implies (1)

A residually finite group has trivial, and therefore torsion-free, finite
residual. For a word-hyperbolic group the finite-carrier argument makes it
virtually torsion-free. Its contrapositive proves (2) implies (1).

## Proof of (1) implies (2)

Let `G` be word-hyperbolic with `R_f(G)!={1}`. If the finite residual already
contains nonidentity torsion, the elementary normal-core argument shows
that `G` itself witnesses (2).

Otherwise choose `1 != g in R_f(G)`; it has infinite order. Set `E=E(g)`.
The subgroup `E` is infinite virtually cyclic. Choose an infinite cyclic
subgroup `D<=E` of finite index. The powers of `g` act on the finite coset
set `E/D`, so some positive power `g^a` belongs to `D`; it is nontrivial
because `g` has infinite order. Every nontrivial subgroup of the infinite
cyclic group `D` has finite index. Thus `<g> intersect D` has finite index
in `D` and in `E`, and `<g>` has finite index in `E`.

Take the normal core `C=core_E(<g>)`. Since `<g>` has finite index in `E`,
the core is normal and has finite index in `E` and in `<g>`. Thus
`C=<g^k>` for a positive integer `k`. For every positive integer `j`, the
subgroup

```text
N_j = <g^(kj)>
```

is characteristic in `C` (the unique subgroup of index `j` in an infinite
cyclic group), hence normal in `E`. Moreover
`[E:N_j]=[E:C]j` is finite.

Use the relative structure `{ {1}, E }` from Osin's elementary-subgroup
theorem. The filling theorem supplies a finite forbidden set
`B subset E minus {1}`. Fill the trivial peripheral trivially. Define

```text
M = max({1} union {|a| : a is an integer and g^a in B}).
```

This maximum exists: `B` is finite, and distinct powers of `g` are distinct.
For `kj>M`, the subgroup `N_j` avoids `B`. In fact, any element of
`N_j intersect B` would be `g^(kjb)` for some nonzero integer `b`, giving
`kj<=|kjb|<=M`, a contradiction.

Therefore the filling

```text
pi_j:G -> Q_j=G/normal_closure_G(N_j)
```

is relatively hyperbolic with peripherals `{ {1}, E/N_j }`, and the
natural homomorphism `E/N_j -> Q_j` is injective. The peripheral quotient
`E/N_j` is finite; `Q_j` is finitely generated as a quotient of `G`. By
Osin's Corollary 1.2, `Q_j` is word-hyperbolic.

For an integer `b`, the equality `(g N_j)^b=N_j` holds exactly when
`g^b in <g^(kj)>`, that is, when `kj` divides `b`. Thus `g N_j` has order
exactly `kj`. Peripheral injectivity shows that `pi_j(g)` has the same
order in `Q_j`, and this order exceeds one. Since `g in R_f(G)`, the
finite-quotient fact proved above gives `pi_j(g) in R_f(Q_j)`. Every
finite-index subgroup of `Q_j` contains this nonidentity torsion element,
so no such subgroup is torsion-free. This proves (2).

The exact order also shows that any prescribed positive integer can divide
the resulting order: restrict `j` to sufficiently large multiples of that
integer. Each `Q_j` here is infinite, because a finite group has trivial
finite residual, whereas `pi_j(g)` is a nonidentity element of its residual.

## Scope and audit corrections

The published equivalence predates this proof. Daniel T. Wise,
*Complete square complexes*, Comment. Math. Helv. **82** (2007), 683--724,
[DOI 10.4171/CMH/107](https://doi.org/10.4171/CMH/107), Proposition 9.2 and
Theorem 9.3, supplies the power-quotient version already imported in
`universal-hyperbolic-vtf-iff-rf-proof`. The proof above verifies the
specific Osin route requested here, including normality of the cyclic
filling subgroup and exact survival of the residual element.

The former route said that injectivity on `{g}` ensured `pi_j(g)!=1`.
Injectivity on a singleton is vacuous. Peripheral injectivity now supplies
the stronger exact-order conclusion. If the independent finite-set clause
is used elsewhere, preserving a nonidentity witness requires injectivity on
`{1,g}`. Also, the explicit bound `kj>M>=1` covers an empty forbidden set
and rules out the unhelpful filling exponent one.

No actual non-residually-finite or non-virtually-torsion-free hyperbolic
group has been exhibited by these implications. For a contemporary
primary-source status check, the 2026 paper
[*Automorphisms of relatively hyperbolic groups and the Farrell--Jones
conjecture*](https://link.springer.com/article/10.1007/s00208-026-03431-7)
still describes universal residual finiteness for hyperbolic groups as an
open question. The existence nodes therefore remain conditional on a
witness; a cycle of the two true implications supplies none.
