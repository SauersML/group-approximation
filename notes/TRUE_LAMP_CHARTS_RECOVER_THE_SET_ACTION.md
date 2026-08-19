# Lamp charts recover the set action — Clifford lamps included

Date: 2026-08-14

## 1. Outcome

`notes/NOTEPAD.md` (section "The 2026 sofic-action permanence theorem cannot
make the Kun--Thom lamp hyperlinear", near line 20344) proves:

> **Lemma (single lamps recover the set action).**  Let `G` act on a set `X`,
> put `D=directSum_X C_2` with `G` permuting coordinates.  If this
> automorphism action is a sofic `C`-action in the sense of
> Alekseev--Bradford Definition 4.23, for any class `C` of groups whatsoever,
> then the original action `G` on `X` is a sofic action on a set.

This note records the one-line observation that the same proof applies
verbatim when the commuting lamp group `D` is replaced by **any** lamp group
whose generators are indexed by `X` and permuted by `G` — in particular by
the Clifford lamp group

```text
C(X)=<z,a_x | z^2=1,[z,a_x]=1,a_x^2=1,[a_x,a_y]=z (x!=y)>,   (LC1)
```

and by every invariant-graph lamp group `Vtilde_S` of
`invariant-graph-clifford-phase`.

Consequently the halo/chart permanence route is closed on the Clifford side
exactly as it is on the Bernoulli side, and no relabelling of the coset
coordinates by Clifford, Pauli, unitary, or other finite-dimensional data can
reopen it.

## 2. The argument, and why the lamp algebra is irrelevant to it

Fix finite `F subset G`, `Z subset X`, and `epsilon>0`.  Definition 4.23
supplies a finite state set `A`, a good subset `S` of states, a target group
`Lambda in C`, an `(F,epsilon)`-multiplicative `varphi:G->Sym(A)`, and
injective partial homomorphisms `pi_s:E->Lambda` satisfying the exact
covariance equation on the prescribed window, where `E` is any prescribed
finite subset of the lamp group.

Take `E` to contain the identity, the single-coordinate lamps

```text
a_z,  z in Z,                                          (LC2)
```

and the finitely many products needed for partial-homomorphism closure.  Put

```text
B=union_(s in S) pi_s({a_z:z in Z}),                    (LC3)
```

a finite set, and `j_s(z)=pi_s(a_z)`.  Injectivity of `pi_s` makes
`j_s:Z->B` injective.  The only property of the lamp group used is that the
automorphism induced by `g` sends `a_z` to `a_(gz)`; the covariance equation
of Definition 4.23 is then literally the orbit-approximation equation for the
maps `j_s`, and `varphi` witnesses soficity of `G` acting on `X`.

Three features of the commuting lamp group are **not** used: commutativity,
the value of `a_z^2`, and the presence or absence of a central element.  So
the proof transfers unchanged to `(LC1)`, where `g` still sends `a_x` to
`a_(gx)`, and to every `Vtilde_S`.  A central element `z`, if present, may
simply be added to `E`; it is fixed by every automorphism and contributes
nothing to `(LC3)`.

## 3. Consequences

1. **Alekseev--Bradford permanence is inapplicable to the Clifford lamp.**
   Their Theorem 5.1 / Corollary 5.2 would make `C(X) semidirect G`
   hyperlinear from a sofic `C`-action on `C(X)`; by Section 2 that
   hypothesis forces the Kun--Thom coset action to be sofic, which
   `coordinate-action-not-sofic` (Kun--Thom Corollary D) refutes.  The same
   applies to Gao--Kunnawalkam Elayavalli--Patchell Theorem 3.8 through its
   sofic-action hypothesis.

2. **Changing the target class does not help.**  This is the point of
   `notes/FALSE_HALO_ACTION_AUDIT.md`: by its locally-sofic collapse theorem
   `(HAA4)`, witnesses with locally sofic targets — finite groups, finite
   Clifford groups, finitely generated subgroups of `U(n)` (linear, hence
   residually finite by Malcev, hence sofic) — already give a sofic
   `C`-action with `C` the sofic class.  Combined with Section 2: any chart
   system with locally sofic targets proves the coset action sofic.  A
   hyperlinear-action proof would need, at some finite test, a target group
   that is *itself* a finitely generated hyperlinear nonsofic group — the
   problem one started with.

3. **Circularity hazard, stated precisely.**  A programme that keeps
   Definition 4.23's shape and only relabels the lamps is circular.  What is
   not circular is changing the *approximating maps* themselves — replacing
   `varphi:G->Sym(A)` by normalized-Hilbert--Schmidt approximate
   representations that do not normalize any masa — and proving that label
   extraction `(LC3)` fails there.  That is exactly the non-Cartan
   requirement recorded at `notes/NOTEPAD.md` line 5891, and it is where the
   difficulty is conserved.

4. **What survives for the Clifford lane.**  The Clifford crossed product is
   still not obstructed by this: the obstruction is to a *method*, not to the
   algebra.  `Cl(X)` is a `II_1` factor with no `G`-invariant Cartan, so a
   Connes embedding of `Cl(X) crossed_product G` cannot be converted into
   charts of the form `(LC3)`; there is nothing in it to extract labels from.
   The lemma above says that any construction which *does* admit such an
   extraction is refuted in advance.

## References

* `notes/NOTEPAD.md`, "single lamps recover the set action" (proof
  transcribed there), and line 5891 for the non-Cartan requirement.
* `notes/FALSE_HALO_ACTION_AUDIT.md`, `(HAA3)`--`(HAA5)`.
* Alekseev--Bradford, *Sofic actions, halo products, and metric
  approximations of groups*, arXiv:2601.18742, Definition 4.23, Theorem 5.1,
  Corollary 5.2.
* Gao, Kunnawalkam Elayavalli, Patchell, arXiv:2401.04945, Theorem 3.8.
* Kun--Thom, arXiv:2608.06222, Corollary D, transcribed in
  `research/artifacts/kun-thom-2608-06222-verified.md`.
