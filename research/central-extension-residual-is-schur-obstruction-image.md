---
rg: 2
id: central-extension-residual-is-schur-obstruction-image
kind: claim
title: The hyperlinear residual of a central extension is the image of the Schur obstruction subgroup, so finite central witnesses exist iff some obstruction subgroup is not divisible
distinct_from:
  hyperlinear-shadow-schur-cokernel-criterion: that computes D(G)=coker(H_2 G -> H_2 Q) for a witness G and leaves the divisible case open; this puts one intrinsic subgroup B(Q) inside H_2 of every hyperlinear base, proves Res(E)=delta(B(Q)) for every central extension and delta_G(B(Q))=D(G) for every witness, and turns the open gap into the single statement "every B(Q) is divisible".
  torsion-dense-schur-multiplier-compiles-twisted-nonce: that approximates one non-CE class by torsion classes when the class kills R_fin(H_2); this shows the exact finite-witness test is non-divisibility of B(Q) itself, which also succeeds when B(Q) lies inside R_fin(H_2 Q), through a change of base to E_Q/B(Q).
  ce-twist-set-is-a-hecke-stable-closed-subgroup: that proves the CE twists of a finitely presented group form a closed subgroup with Hecke symmetry; this uses the subgroup property for arbitrary countable hyperlinear groups and computes the residual of every central extension from its annihilator.
  twisted-factor-existence-is-equivalent-to-nonhyperlinearity: that allows non-hyperlinear bases; here the base is hyperlinear, where the CE set contains 0 and becomes a subgroup.
---

**Setup.** `Q` is a countable hyperlinear group, `A = H_2(Q;Z)`, and
`Hom(A,T)` carries the pointwise topology (compact, metrizable). Write
`Q = F/R` with `F` free. A *twist* is an `F`-invariant homomorphism
`lambda : R -> T`; `L_lambda(Q)` is the GNS algebra of the trace
`tau_lambda(w) = lambda(w)` for `w in R`, `0` otherwise, on `C*(F)`. Its
Connes embeddability depends only on the class
`chi = lambda|_(R cap [F,F]) in Hom(A,T)`. Put

```text
W(Q) = { chi in Hom(A,T) : L_chi(Q) is Connes embeddable },
B(Q) = { a in A : chi(a) = 0 for all chi in W(Q) }.            (SO0)
```

Call `B(Q)` the *Schur obstruction subgroup* of `Q`.

**Statement.**

1. **(Annihilator.)** `W(Q)` is a closed subgroup of `Hom(A,T)`, and
   `W(Q) = ann B(Q)`. A twist is CE iff its class kills `B(Q)`.
2. **(Residual formula.)** Let `1 -> C -> E -> Q -> 1` be a central
   extension with `C` countable, and let `delta_E : A -> C` be its
   transgression (the five-term connecting map). Then

   ```text
   Res(E) = delta_E(B(Q)).                                      (SO1)
   ```

   In particular `E` is hyperlinear iff `delta_E(B(Q)) = 0`.
3. **(Every witness is hit by the obstruction.)** For every countable `G`
   with hyperlinear shadow `Q = G/Res(G)`, the transgression
   `delta_G : A -> D(G)` maps `B(Q)` onto `D(G)`:

   ```text
   H_2(Q) = B(Q) + im( H_2(G) -> H_2(Q) ).                      (SO2)
   ```

4. **(Realization.)** There is a central extension `E_Q` of `Q` by `A` whose
   transgression is the identity. It has `Res(E_Q) = D(E_Q) = B(Q)`, and its
   shadow is `H_Q = E_Q/B(Q)`.
5. **(Exact normal form of the gap.)** Let (C) be "some countable hyperlinear
   group has a non-hyperlinear central extension" and (F) "some countable
   hyperlinear group has a non-hyperlinear central extension by `Z/p`". Then
   - (C) iff `B(Q) != 0` for some hyperlinear `Q`;
   - (F) iff `B(Q)` is not divisible for some hyperlinear `Q`
     iff `B(Q)` is not contained in `R_fin(H_2 Q) = intersection_m m H_2(Q)`
     for some hyperlinear `Q`.

   So the divisible gap of `hyperlinear-shadow-schur-cokernel-criterion` is
   exactly: every obstruction subgroup `B(Q)` is divisible, and some is
   nonzero. If `B(Q)` is not divisible, the witness is the central extension
   `E_Q/B'` of the hyperlinear group `H_Q` by `B(Q)/B' = Z/p`.
6. **(Perfect bases carry totally non-CE multipliers.)** If `Q` is perfect,
   `E_Q` is the universal central extension, `H_Q` is perfect,
   `H_2(H_Q) = B(Q)`, and `B(H_Q) = H_2(H_Q)`: every nontrivial twist of
   `H_Q` is non-CE.
7. **(Cover transfer.)** Let `Q = F/R` with `F` finitely generated, let
   `lambda` be a non-CE twist, and let `R_n <= R` be normal in `F` with
   `R_n -> R` in the Chabauty topology and `Q_n = F/R_n` hyperlinear. Then
   for all large `n`, `lambda|R_n` is a non-CE twist of `Q_n`, so
   `B(Q_n) != 0`. If moreover `lambda(R_n)` is finite for infinitely many
   `n`, or `H_2(Q_n)` is residually finite (for example `Q_n` finitely
   presented) for infinitely many `n`, then (F) holds.

**Biography of a divisible-gap counterexample.** Suppose (C) holds and (F)
fails. Then for every hyperlinear `Q`, `B(Q)` is a divisible group
(`Q^(r) + sum_p Z(p^infty)^(r_p)`), and `D(G) = delta_G(B(Q))` for every
witness `G`. For every finitely generated hyperlinear `Q` with a non-CE twist
`lambda`, every sequence of hyperlinear covers `Q_n -> Q` converging to `Q`
has, for all large `n`, infinite `lambda(R_n)`, a non-residually-finite
`H_2(Q_n)` and a nonzero divisible `B(Q_n)`. In particular the finitely
presented covers of `Q` are eventually non-hyperlinear.

**Routes the normal form kills.**
- *Real 2-classes with an open set of non-CE parameters* (option 1 of the
  open gap). For `omega in Hom(A,R)` the set `{t : e(t omega) in W(Q)}` is a
  closed subgroup of `R`, so it is `R` or discrete. One non-CE `t` already
  gives an open dense set of them; this is equivalent to
  `omega(B(Q)) != 0`, i.e. to (C) on `Q`, and gives no finite witness when
  `B(Q)` is divisible.
- *Transport of an obstruction along maps.* Images of divisible groups are
  divisible. Every `B(Q')` produced as an image of `B(Q)` (subgroup
  inclusions `Q <= Q'`, which satisfy `i_* B(Q) <= B(Q')`, transgressions
  `delta_E`, pushouts along `C -> C/C'`) is divisible whenever `B(Q)`
  is. A finite witness needs a hyperlinear group whose obstruction subgroup
  is not generated by such images.

**Calibration.**
- Amenable `Q`: all twisted algebras are hyperfinite, `B(Q) = 0`, and (SO1)
  says every central extension is hyperlinear, as it is (amenable).
- Finitely presented `Q`: `A` is finitely generated, so its divisible
  subgroups are `0`. Item 5 reproduces "non-CE twist on a finitely presented
  hyperlinear group gives a finite central witness".
- Non-hyperlinear central extension `E` of `H` by finite `C`: (SO1) gives
  `B(H) != 0` with finite image, so `B(H)` is not divisible, matching item 5.
- Witness with `Q = 1` (simple witness): `A = 0`, and (SO2) reads `0 = 0`.

No novelty is claimed for the direct-integral decomposition along a central
subgroup or for the subgroup property; the content is (SO1), (SO2), the
realization and the exact normal form of the gap.
