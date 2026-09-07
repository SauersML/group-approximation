# A linear relator certificate for the full MF radical

2026-09-07.  Audit and re-derivation of an external dossier proposing a
quantitative strengthening of the full-MF-radical conclusion of
`non_mf_groups_exist.tex`.  Every displayed statement below was re-derived
here; the section headed *Corrections* lists the three places where the
dossier and this audit disagree.

Throughout, `G = <g_1,...,g_m>` is finitely generated, `F_m` is free on
`x_1,...,x_m`, and for a unitary tuple `U = (U_1,...,U_m) in U(d)^m` and a
finite set `R subset F_m`,

```text
D(U)     = max_i ||U_i - I||_op,
Def_R(U) = max_(r in R) ||r(U) - I||_op.
```

`Res_MF(G) = G` abbreviates the manuscript's hypothesis that every
homomorphism from `G` to an MF group is trivial.  By
Lemma~\ref{prop:mf-residual-calculus} of the manuscript this is equivalent
to every corona homomorphism `G -> U(prod_n M_(d_n) / sum_n M_(d_n))` being
trivial, and that is the form used below.

## 1.  The proposition

**Proposition.**  Let `G` be finitely generated with `Res_MF(G) = G`.  Then
there are finitely many `r_1,...,r_s in F_m` with `r_j(g) = 1` and a
constant `C > 0` such that for every `d >= 1` and every
`U in U(d)^m`,

```text
D(U) <= C max_j ||r_j(U) - I||_op.                     (*)
```

Conversely, if some finite set of relations of `G` and some `C` satisfy
`(*)`, then `Res_MF(G) = G`.

No finite presentability is assumed; the finite relator list is produced,
not given.  Neither the list nor `C` is asserted computable.

## 2.  Proof, in two halves

The dossier proves this by one diagonal contradiction.  The argument splits
cleanly into an explicit half and a compactness half, and the split is worth
keeping because only the second half is non-effective.

### 2.1  Perfectness and the quadratic self-improvement (explicit)

`G` is perfect.  Otherwise the abelianization is a nontrivial finitely
generated abelian group, so it surjects onto a nontrivial finite cyclic
group; a finite group `F` embeds in some `U(k)` by the regular
representation and then in the corona by constant sequences (the class of
`(V,V,...)` differs from `1` by `||V - I||_op > 0`), so `F` is MF, and the
composite is a nontrivial homomorphism from `G` to an MF group.

Fix words `a_(ik), b_(ik) in F_m` with

```text
g_i = prod_(k=1)^(q_i) [a_(ik)(g), b_(ik)(g)],
w_i = x_i^(-1) prod_(k=1)^(q_i) [a_(ik), b_(ik)],
W   = {w_1,...,w_m},
B   = 2 max_i sum_(k=1)^(q_i) |a_(ik)| |b_(ik)|.
```

Two elementary bounds.  For unitaries, `||V_1...V_k - I|| <= sum_j ||V_j - I||`
and `||U_i^(-1) - I|| = ||U_i - I||`, so `||a(U) - I|| <= |a| D(U)`.  And

```text
||[A,B] - I|| = ||AB - BA|| = ||(A-I)(B-I) - (B-I)(A-I)||
             <= 2 ||A - I|| ||B - I||.
```

Since `U_i w_i(U) = prod_k [a_(ik)(U), b_(ik)(U)]`, the distance from `U_i`
to that product is `||w_i(U) - I||`, and the product is within
`sum_k 2|a_(ik)||b_(ik)| D(U)^2` of `I`.  Taking the maximum over `i`,

```text
D(U) <= Def_W(U) + B D(U)^2                            (Q1)
```

for every dimension and every unitary tuple.  On the region
`D(U) <= 1/(2B)` the quadratic term absorbs, and

```text
D(U) <= 2 Def_W(U).                                    (Q2)
```

`(Q1)` and `(Q2)` use only perfectness together with a chosen commutator
expression of the generators.  `B` is explicit once that expression is
chosen.

### 2.2  The threshold (compactness)

**Claim.**  There are a finite `R_0 subset F_m` of relations of `G` and
`delta > 0` such that `Def_(R_0)(U) < delta` forces `D(U) <= 1/(2B)`.

Suppose not.  Enumerate the relations of `G` as `R_1 subset R_2 subset ...`,
finite and exhausting, and pick `U^((n)) in U(d_n)^m` with
`Def_(R_n)(U^((n))) < 1/n` and `D(U^((n))) > 1/(2B)`.  Every fixed relation
of `G` lies in `R_n` for large `n`, so its defect along the sequence tends
to `0`, and `x_i mapsto [U_i^((n))]_n` descends to a corona homomorphism
`G -> U(prod_n M_(d_n) / sum_n M_(d_n))`.  The hypothesis makes it trivial,
so `D(U^((n))) -> 0`, contradicting the choice.

### 2.3  Gluing

Put `R = R_0 union W` and `C = max(2, 2/delta)`.  If `Def_R(U) < delta`
then `D(U) <= 1/(2B)`, so `(Q2)` gives `D(U) <= 2 Def_W(U) <= 2 Def_R(U)`.
Otherwise `D(U) <= 2 <= (2/delta) Def_R(U)`, using `||V - I||_op <= 2` for
unitaries.  Either way `(*)` holds with that `C`.

### 2.4  Converse

Let `phi: G -> M` with `M` MF, and embed `M` in the unitary group of a
corona.  Lift `phi(g_i)` to unitaries: a lift `a` of a unitary satisfies
`a^*a - 1 in sum_n M_(d_n)`, so `a` is invertible after correcting finitely
many coordinates, and the polar part of an invertible element of the finite
von Neumann algebra `prod_n M_(d_n)` is unitary and differs from `a` by an
element of the ideal.  Each `r_j` is a relation of `G`, so
`||r_j(U^((n))) - I|| -> 0`; then `(*)` gives `D(U^((n))) -> 0`, which says
`phi(g_i) = 1` for every `i`.

## 3.  Consequences

**Finitely presented cover.**  With `r_1,...,r_s` as in `(*)` put
`P = <x_1,...,x_m | r_1,...,r_s>`.  The relators of `P` are among those of
`G`, so `P` surjects onto `G`, and `(*)` holds verbatim for `P`, so the
converse gives `Res_MF(P) = P`.  Every finitely generated group with full
MF radical is therefore a quotient of an `m`-generated finitely presented
group with full MF radical.  The statement preserved is the one about *all*
homomorphisms to MF groups, which is stronger than producing a finitely
presented non-MF cover.

**Openness in the space of marked groups.**  In the space `G_m` of
`m`-marked groups, `{H : r = 1 in H}` is clopen for each fixed word `r`, so
the set of marked groups satisfying `r_1,...,r_s` is a clopen neighbourhood
of `(G, (g_i))`, and by the converse every member of it has full MF radical.
Full MF radical is an open condition on `G_m`.  Adding one inequation
`v != 1` keeps the set clopen and makes every member nontrivial.

**Relative Hull quotients.**  Let `G` be finitely presented, torsion-free,
acylindrically hyperbolic, and let `Omega subset G` be finite.  Apply
`common-quotient-onto-normal-subgroup` with `G_1 = G`, `G_2 = Q` the group
of the manuscript's torsion-free theorem, `D = Q`, and `F_1 = Omega`.  The
common quotient `P` is acylindrically hyperbolic with trivial finite
radical, torsion-free, finitely presented, and `alpha_1|_Omega` is
injective; as a quotient of `Q` it is two-generated, has property (T), and
has full MF radical.  Taking `G = F_2` and `Omega` the ball of radius `n`
gives such groups of girth greater than `n` in the inherited two-generator
marking.

**Reduced C\*-algebra of `Q`.**  `Q` is acylindrically hyperbolic and
torsion-free, so its finite radical is trivial, and `C*_r(Q)` is separable,
unital, generated by two unitaries, simple with a unique tracial state
(Dahmani--Guirardel--Osin, Theorem 2.35, with Breuillard--Kalantar--Kennedy
--Ozawa, Theorem 1.4), of stable rank one (Gerasimova--Osin,
arXiv:1910.14524, Theorem 1.1: for acylindrically hyperbolic `G_i` with
`K(G_i) = 1`, `sr(C*_r(G_1 x ... x G_k)) = 1`), stably finite because the
canonical trace is faithful, and not MF by the manuscript's reduced
C\*-consequence.

## 4.  Corrections to the dossier

1.  Simplicity and unique trace are not a consequence of
    Dahmani--Guirardel--Osin Theorem 2.35 alone.  Gerasimova--Osin state the
    chain as "[DGO, Theorem 2.35] and [BKKO, Theorem 1.4]"; DGO 2.35
    identifies the amenable radical of an acylindrically hyperbolic group
    with its finite radical, and BKKO 1.4 converts a trivial amenable
    radical into the unique trace property.  Both citations are needed.

2.  The dossier proposes to obtain the relative quotient by "Hull's common
    quotient construction", and asserts that it preserves torsion-freeness
    and finite presentability.  Those two preservation clauses are not in
    Hull's Corollary 7.4 as printed; they are clauses 3 and 4 of the
    established node `common-quotient-onto-normal-subgroup`, whose route
    derives them from Hull Theorem 7.1(e) and from the fact that the
    finitely generated case of Corollary 7.4 uses two applications of
    Theorem 7.1 and never the direct limit of Corollary 7.3.

3.  The dossier's claim that `C*_max(Q)` inherits the manuscript's proper
    isometry is **not** recorded.  Proposition~\ref{prop:max-infinite}
    needs a property-(T) subgroup `Gamma <= Q` and `t` with
    `t Gamma t^(-1) subsetneq Gamma` strictly, and the saturation quotient
    does not carry that configuration forward.  Only the reduced algebra is
    claimed here.

## 5.  Novelty sweep

Searched before authoring.  The nearest existing nodes and what separates
them:

- `uniform-finite-mf-obstruction`: finite test set and positive threshold,
  for the manuscript's literal group and one marked word.  Threshold form,
  one word, one group.
- `hyperlinear-radical-presentation-compactness`: the normalized
  Hilbert--Schmidt analogue, in `epsilon`--`delta` form with the finite
  window depending on `epsilon`.
- `depthwise-opnorm-collapse-implies-mf-radical`: the converse direction,
  with a sequence of finite tests and unrestricted constants.
- `full-mf-radical-finite-challenge-cylinder`: the clopen cylinder around
  the already finitely presented `Q`, using its given presentation.
- `clopen-non-mf-cylinder`: the eight-generator literal cylinder, concluding
  non-MF.
- `exact-stably-finite-non-mf-reduced-group-algebra`: `C*_r(W)`, with
  exactness, no simplicity, no unique trace, no stable rank.

What none of them states is a single global inequality, linear in the
relator defect, with a fixed finite relator set independent of the
tolerance, for an arbitrary finitely generated group with full MF radical.

## 6.  What is not proved

`(*)` is an existence statement.  The proof produces neither an explicit
relator list nor a numerical `C`; `B` in `(Q1)` is explicit, `delta` in
2.2 is not.  Making `delta` explicit for the binary Leavitt group or for
`Q` is the content of `effective-transport-modulus` and is open.
