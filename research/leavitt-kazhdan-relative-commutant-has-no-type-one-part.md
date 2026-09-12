---
rg: 2
id: leavitt-kazhdan-relative-commutant-has-no-type-one-part
kind: claim
title: In every nontrivial tracial model of the Leavitt group the Kazhdan relative commutant absorbs a Thompson factor and has no type I part
distinct_from:
  transported-gap-masa-kills-leavitt-hs-models: that shows a masa of the Kazhdan relative commutant cannot be carried back into it by the compressor; this is an unconditional structure theorem for that commutant in every nontrivial model, forcing type II_1 and tensor absorption of L(V).
  relative-wall-commutant-growth: that is the algebraic equivalence between a relative wall and strict growth of the commutant under a compressor; this identifies the growth as a tensor factor L(V) and draws the type consequence.
  corona-commutant-no-growth: that is the refuted operator-norm no-growth question in a norm corona; this is a tracial statement about what the growth must contain.
---

**ESTABLISHED.**  Use the nine-leaf configuration of
`openai-nine-leaf-leavitt-configuration`:

* `R = L_(F_2)(1,2)`, with `Gamma = EL_alpha(R) <= G = EL_D(R)` and compressor `u`;
* `J = V_(1000) ~= V`, and `V_1 = u J u^(-1) <= Gamma`.

Let `(M,tau)` be a finite von Neumann algebra and `sigma : G -> U(M)` a
homomorphism with `tau o sigma != 1`.  By `binary-leavitt-full-character-simplex`,
`tau o sigma = lambda + (1 - lambda) delta_e` with `lambda < 1`.  So
`sigma(G)''` has a central projection `q` with `tau(q) = 1 - lambda > 0` on
which the character is regular.  Compressing by `q` gives a regular-character
model.  For such a model put

```text
A_0 = sigma(Gamma)' cap M,   A_k = sigma(u)^k A_0 sigma(u)^(-k).
```

Then:

1. `sigma(V_1)'' ~= L(V)` is a II_1 factor, contained in `A_1 cap A_0'`.
2. `A_0 v sigma(V_1)'' ~= A_0 (tensor) L(V)` trace-preservingly, and this
   algebra lies in `A_1 ~= A_0`.  More generally
   `A_0 (tensor) L(V)^(tensor k) <= A_k ~= A_0` for every `k`.
3. `A_0` has no type I summand; it is of type II_1.
4. **Capture sector.**  Suppose exact finite-level centralizers capture the
   commutant, `A_0 = prod_omega A_n` with `A_n` finite dimensional.  Then for
   every `m`, the trace mass of the summands `M_j (tensor) 1` of `A_n` with
   `j <= m` tends to `0` along `omega`.  Captured Kazhdan commutants of a
   nontrivial model therefore have diverging block sizes on almost all mass.

**Use.**  Item 3 is a screen for unstable-branch constructions
(`leavitt-steinberg-hs-unstable`, `binary-leavitt-unit-group-hyperlinear`).
Any model in which the approximate commutant of the `Gamma`-generators has
bounded multiplicity on positive mass is trivial.  The masa collapse of
`transported-gap-masa-kills-leavitt-hs-models` is the multiplicity-one case.

**Checked against false consequences.**

* *The Thompson factor is the input.*  With a finite nonabelian commuting `J`,
  `sigma(J)''` is finite dimensional and none of items 2--4 follows.  So the
  theorem makes no claim about sofic compression configurations with LEF
  finite factors.
* *Soficity is not used.*  The theorem does not assert that `G` is
  nonhyperlinear.  It is a necessary condition on faithful models.

Derivation: `leavitt-kazhdan-relative-commutant-no-type-one-proof`.
