# C-star regularity does not automatically promote the marked trace

Date: 2026-08-23

## Verdict

For a finite-dimensionally invisible central mark, the proposed C-star
regularity shortcut splits cleanly into one genuinely useful hypothesis and
several false promotions.

| hypothesis on the relevant algebra | what it actually gives |
|---|---|
| exactness | no promotion of a hyperlinear trace to an MF trace |
| local reflexivity | no such promotion; exact algebras are locally reflexive |
| property `(T)` | repairs **amenable/ucp** trace models to a finite-dimensional quotient, not arbitrary hyperlinear models |
| quasidiagonal trace | enough, since it is an MF trace (and amenable), but this is already the missing conclusion in stronger form |
| quasidiagonal algebra | supplies some amenable trace; it selects the canonical one only under an additional trace-selection hypothesis such as unique trace |
| MF algebra | supplies some trace from a matrix corona, not necessarily the canonical trace; even an MF trace is asymptotic data, not an honest finite-dimensional representation |
| LLP of the full group C-star algebra | genuinely enough for a non-residually-finite Kazhdan group, by weak-ucp stability; for the binary Leavitt unit group all standard permanence routes are already fenced |

Thus the useful statement is not

```text
hyperlinear canonical trace + ordinary C-star regularity
    => finite-dimensional traces seeing the mark.
```

The useful statement is the much stronger lifting/repair assertion supplied
by LLP (or directly by normalized-Hilbert--Schmidt stability).  Neither
exactness nor local reflexivity supplies it.

## 1. Exactness and local reflexivity are refuted inside this repository

Let `W` be the concrete sofic non-MF witness used by
`exact-stably-finite-non-mf-reduced-group-algebra`, and put

```text
A = C*_r(W),                 tau = the canonical reduced trace.
```

The manuscript proves that `A` is separable and exact and that `tau` is
faithful.  Since `W` is sofic, `L(W)` embeds trace-preservingly in `R^omega`;
therefore the GNS von Neumann algebra of `(A,tau)` is Connes embeddable and
`tau` is hyperlinear.  If `tau` were an MF trace, pull it back along

```text
C^*(W) -> C*_r(W).
```

MF traces pull back under star-homomorphisms.  The resulting MF canonical
trace on `C^*(W)` would make `W` operator MF by
`regular-character-mf-trace-implies-group-mf`, contradicting the defining
property of `W`.  Hence `tau` is a faithful hyperlinear non-MF trace on an
exact algebra.

Kirchberg's theorem that exact C-star algebras are locally reflexive then
gives the same counterexample with local reflexivity included.  This is
strictly sharper than `hyperlinear-trace-not-mf-trace`, whose displayed
choice `C^*(E)` does not itself assert exactness.

Primary source cross-check: Gabe, *Quasidiagonal traces on exact C-star
algebras*, arXiv:1511.02760, before Lemma 4.4, explicitly recalls exactness
`=>` local reflexivity and states the correct local-reflexive theorem:

```text
tau amenable  <=>  pi_tau(A)'' hyperfinite.
```

It says **hyperfinite**, not merely Connes embeddable.  This is the precise
place where replacing an amenable trace by a hyperlinear trace breaks the
argument.

## 2. Thom's exact LEF Kazhdan group is the decisive exactification no-go

The preceding trace counterexample does not use property `(T)`.  Thom's first
example in *Examples of hyperlinear groups without factorization property*,
arXiv:0810.2180, supplies a counterexample tailored to marked exactification.

Fix a prime `p`, let `R=F_p[t,t^{-1}]`, let `G'=G_0(R)` be Thom's displayed
five-by-five matrix group, and identify

```text
Z(G') = direct_sum_(n in Z) F_p t^n.
```

Put

```text
C = direct_sum_(n>=0) F_p t^n,       G=G'/C,
j = the class of e_15(t^{-1}).
```

Conjugation by `diag(t,1,1,1,1)` induces a surjective endomorphism
`alpha:G->G` whose kernel is the central copy `F_p t^{-1}`.  In particular
`j` is central, has order `p`, and is nontrivial.  Thom proves that `G` is
finitely generated, has property `(T)`, and is LEF.  His LEF lemma is
especially strong: every finite `F subset G` embeds multiplicatively on
`F^2` into one finite group.

### The whole kernel is finite-residually invisible

This useful strengthening of the usual non-Hopfian argument is elementary.
Let `q:G->Q` be any finite quotient.  The maps `q alpha^n` are all surjective
onto `q(G)`, so their kernels all have the same finite index.  A finitely
generated group has only finitely many subgroups of a fixed finite index;
choose `m<n` with

```text
ker(q alpha^m)=ker(q alpha^n).
```

Surjectivity of `alpha^m` lets us cancel its inverse image and gives

```text
ker(q)=ker(q alpha^(n-m)).
```

Consequently `ker(alpha) <= ker(q)`, and in particular `q(j)=1`.

Now let `rho:G->U(d)` be any finite-dimensional unitary representation.  Its
image is a finitely generated complex linear group, hence residually finite
by Malcev.  If `rho(j)!=1`, a finite quotient of `rho(G)` would separate it,
contradicting the preceding paragraph.  Thus

```text
rho(j)=I             for every finite-dimensional rho.       (CR1)
```

On the other hand, LEF gives, for every finite window containing `j`, an
**exactly multiplicative** finite-group regular model in which `j` is not the
identity.  Hence even

```text
property (T) + exact local finite models + central fd-invisibility
```

does not exactify the local models into representations of the whole group.
This is the precise model-theoretic no-go needed for the Leavitt mark: property
`(T)` controls Hilbert-space almost-invariance, but it is not matricial
stability.

The group `G` is exact as well.  Projection onto the middle `3 x 3` block
expresses it as an extension of `SL_3(R)` by an amenable nilpotent group (the
upper unipotent radical modulo `C`).  The quotient is a countable linear group
and hence exact by Guentner--Higson--Weinberger; exactness is closed under
extensions by amenable kernels.

## 3. The nontrivial reduced central fibre has every tempting property except the right one

Choose a nontrivial character `chi:<j>->T` and form the central projection

```text
p_chi = (1/p) sum_(k=0)^(p-1) conjugate(chi(j^k)) lambda(j^k)
```

in `C*_r(G)`.  Set

```text
B_chi = p_chi C*_r(G),
tau_chi(x) = tau_G(x)/tau_G(p_chi) = p tau_G(x).
```

Then:

1. `B_chi` is separable, unital, exact, and locally reflexive.
2. It has C-star property `(T)`: it is a unital quotient of `C^*(G)`, and
   property `(T)` passes to quotients.
3. `tau_chi` is faithful and hyperlinear.  Indeed `G` is LEF, hence
   hyperlinear, so `L(G)` embeds in `R^omega`; Connes embeddability passes to
   the nonzero corner `p_chi L(G)`.
4. `B_chi` has no nonzero finite-dimensional representation.  Such a
   representation would pull back to a representation of `G` on which `j`
   acts as the nontrivial scalar `chi(j)`, contradicting `(CR1)`.
5. `B_chi` has no amenable trace, by Brown's property-`(T)` theorem
   (`property-t-cstar-amenable-trace-forces-fd-quotient`).  In particular
   `tau_chi` is hyperlinear but nonamenable, and therefore not
   quasidiagonal.  The algebra itself cannot be quasidiagonal either, since a
   unital quasidiagonal algebra has an amenable trace.

This simultaneously disproves the promotions

```text
exact + locally reflexive + property (T) + hyperlinear trace
    => amenable trace,

exact local finite models + property (T)
    => honest finite-dimensional representation.
```

It also explains why Brown's theorem does not start from hyperlinearity:
amenability gives **ucp** Hilbert--Schmidt models and Stinespring dilations;
hyperlinearity gives a homomorphism only after quotienting by the tracial
null ideal.  Local reflexivity does not lift that homomorphism.

## 4. MF and QD: trace selection is load-bearing

An MF embedding of a unital algebra into a norm matrix corona produces at
least one tracial state by composing with an ultralimit of coordinate traces.
It does not force a preassigned trace to be that state.  Therefore

```text
B is MF
```

cannot by itself promote the canonical group trace.  A unique-trace theorem
would remove this selection ambiguity, but even an MF trace consists of
asymptotic operator-norm models, not honest finite-dimensional
representations; `(CR1)` alone does not contradict it.  A further repair
theorem is still necessary.

A quasidiagonal **trace** is different: its ucp operator-norm models make it
both amenable and MF, so it would be enough.  But Section 3 shows that on the
marked property-`(T)` fibre such a trace cannot exist.  A quasidiagonal
**algebra** only selects some amenable trace unless uniqueness pins it; for
`B_chi` even this weaker algebraic property is impossible.

The nuclear route is also unavailable.  Nuclearity makes every trace
amenable, so Brown would force a finite-dimensional quotient of the marked
fibre.  Equivalently, for a reduced group algebra nuclearity would force group
amenability.  The infinite Kazhdan Leavitt candidates are nonamenable.

## 5. LLP is the one genuinely applicable closure theorem

For a non-residually-finite Kazhdan group `H`, LLP of `C^*(H)` turns a
hyperlinear embedding into local ucp lifts.  Stinespring dilation and property
`(T)` then repair these to genuine finite-dimensional representations.  This
is the established claim
`llp-non-rf-kazhdan-group-is-non-hyperlinear`.

Hence LLP of the full C-star algebra of the binary Leavitt unit group would
indeed close the non-hyperlinearity goal.  It is not a consequence of
exactness or local reflexivity, and it is already blocked by
`leavitt-llp-permanence-fence`: subgroup inheritance would imply LLP for
`C^*(F_2 x F_2)`, still an open problem, while the standard directed-union,
amenable-extension, and finite-edge graph-of-groups decompositions become
circular.

So the correct endpoint of the audit is:

```text
LLP(full C^*(Q))                    => goal closes;
exactness/local reflexivity         => false promotion;
property (T) without ucp lifting    => false promotion;
MF algebra without trace selection => insufficient;
QD/amenable canonical trace         => sufficient but impossible on the
                                        fd-invisible property-(T) fibre.
```

No established C-star regularity theorem currently turns the Leavitt
canonical hyperlinear trace into the required finite-dimensional trace.  The
missing content remains a lifting/stability theorem, not an exactness theorem.

## Sources checked

- A. Thom, *Examples of hyperlinear groups without factorization property*,
  arXiv:0810.2180.  Source checked directly: the definition of `G`, the
  central subgroup `C`, the surjective noninjective endomorphism, property
  `(T)`, and the exact LEF-window lemma are all in Section 2 of the submitted
  TeX.  The repository's earlier source record
  `research/artifacts/thom-0810-2180-verified.md` concerns Thom's second
  central-corner theorem; this audit uses the first example and is
  nonduplicate.
- N. P. Brown, *Kazhdan's Property T and C-star-algebras*,
  arXiv:math/0602312, Proposition 5.5/Corollary 5.6 in the published
  numbering: a property-`(T)` C-star algebra has an amenable trace iff it has
  a nonzero finite-dimensional quotient.
- J. Gabe, *Quasidiagonal traces on exact C-star algebras*,
  arXiv:1511.02760, Theorem 3.7 and Lemma 4.4: the positive exactness theorem
  starts from an **amenable** trace; local reflexivity identifies amenability
  with hyperfiniteness of the GNS von Neumann algebra.
- E. Guentner, N. Higson, S. Weinberger, *The Novikov conjecture for linear
  groups*: countable linear groups are exact.
