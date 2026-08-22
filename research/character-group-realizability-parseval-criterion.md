---
rg: 2
id: character-group-realizability-parseval-criterion
kind: claim
title: A character lives in some group factor iff it has a Parseval-normalised joint state with a regular partner
distinct_from:
  algebraic-envelope-principle: that identifies one class of hosts, algebraic compact-abelian crossed products, as group factors on the nose; this characterises realisability in an ARBITRARY group factor by a state condition and records which closure operations the realisable characters admit.
  non-ce-trace-on-sofic-racg: that exhibits a non-CE character on an explicit sofic group; this is the general criterion deciding when such a character's GNS algebra sits inside the group factor of some (other) group.
---

Let `W` be a countable group and `tau` a character of `W`, i.e. a tracial
state on `C^*(W)`, with GNS algebra `Q_tau = pi_tau(W)''`.  Call `tau`
**group-realisable** if there are a countable group `Lambda` and a unital
trace-preserving embedding `Q_tau -> L(Lambda)`; equivalently, a unitary
representation `v : W -> U(L(Lambda))` with `tau_Lambda(v_w) = tau(w)`.

**Theorem (criterion).**  `tau` is group-realisable iff there are a
countable group `Lambda` and a state `psi` on the maximal tensor product
`C^*(W) (x)_max C^*(Lambda)` such that

```text
psi(1 (x) h) = delta_(h,e)          (h in Lambda),            (PGR1)
psi(w (x) 1) = tau(w)               (w in W),                 (PGR2)
sum_(h in Lambda) |psi(w (x) h)|^2 = 1   (w in W).            (PGR3)
```

`(PGR1)` says the `Lambda`-marginal is the regular character, `(PGR2)` that
the `W`-marginal is `tau`, and `(PGR3)` (Parseval) that each `W`-generator
moves the cyclic vector inside the `Lambda`-regular copy.  When it holds,
`v_w` is the convolution operator with Fourier coefficients
`h -> psi(w (x) h^-1)`.

**Closure properties.**  The set `R(W)` of group-realisable characters of
`W` contains every character with hyperfinite GNS algebra (in particular
every finite-dimensional character) and the regular character `delta_e`
(trivially, with `Lambda = W`; its GNS algebra `L(W)` is hyperfinite only
for amenable `W`), and is closed under
convex combinations, pointwise products, pullback along homomorphisms
`W' -> W`, and induction from finite-index subgroups.  It is NOT known to
be weak*-closed.

**Why this matters for the goal.**  A group-realisable character whose GNS
algebra is not Connes embeddable makes its host `Lambda` non-hyperlinear
(CE passes to subalgebras).  Every closure operation above preserves Connes
embeddability of the GNS algebra and produces hosts
(`Lambda_1 x Lambda_2`, `Lambda x Z`, `S_infinity x Lambda`, ...) that are
hyperlinear when the inputs are; so the non-CE characters of
`non-ce-trace-on-sofic-racg` and `non-cohyperlinear-irs-exists` cannot be
reached from the hyperfinite seed by these operations, and any host
realising them is itself a goal witness.  The criterion turns the
transfer problem into a state-existence problem on
`C^*(W) (x)_max C^*(Lambda)` with one non-convex constraint `(PGR3)`; the
weakest sufficient form for the programme is
`non-ru-bcs-is-satisfiable-in-a-group-factor`.

There are two further exact permanence statements at the algebra level.
By `group-realizability-reflects-free-bernoulli-envelopes`, adjoining a free
group-factor leg or forming an untwisted Bernoulli crossed product preserves
**and reflects** group realizability.  In Parseval language, these operations
can transport an already existing joint state but cannot manufacture one:
restriction to the payload leg or to one Bernoulli coordinate recovers a
Parseval witness for the original character algebra.
