---
rg: 2
id: chromatic-codes-kill-marks-in-every-bi-invariant-approximation
kind: claim
title: Bounded-area chromatic codes kill their mark in every totally bounded bi-invariant approximation, so a code with a nontrivial mark proves the group is neither weakly sofic nor hyperlinear
distinct_from:
  infinite-chromatic-commutator-code-kills-mf-mark: that proves the operator-norm corona case only and mentions compact targets in one sentence, with a Lipschitz proviso; this proves the kill in every totally bounded bi-invariant target, including all finite groups, where the collision is exact and no Lipschitz input is needed, and it draws the consequence that a code refutes weak soficity and hyperlinearity.
  bounded-area-conjugacy-difference-code-kills-mf-mark: that says its criterion is tailored to norm-matrix coronas; this shows the same pigeonhole kills the mark in every totally bounded bi-invariant target, so the criterion is not specific to the operator norm.
  bounded-area-high-chromatic-conjugacy-collapse: that is the normalized Hilbert--Schmidt Carmichael criterion for unitary matrices; this puts that criterion, the commutator code and the conjugacy-difference code in one statement about every totally bounded bi-invariant target, finite groups included.
  high-chromatic-sections-force-area-divergence: that forces Carmichael area divergence in hyperlinear groups; this forces the divergence for all three chromatic certificate shapes and over the larger class of groups that survive in some totally bounded bi-invariant approximation, e.g. weakly sofic and finite-field linear sofic groups.
  weak-soficity-survives-every-corpus-obstruction: that surveys mechanisms realized weakly soficly and concludes only the word certificate is left; this identifies the chromatic codes as a second mechanism that no weakly sofic group can carry around a nontrivial mark.
  finite-quotients-bound-carmichael-conjugacy-chromatic-number: that is an exact finite-quotient coloring with no area; this is the approximate version over arbitrary bi-invariant targets, paid for by uniformly bounded area.
---

**Setting.** Let `Gamma=<S|R>` be finitely presented and `z` a word.  A
*target* is a group `K` with a bi-invariant metric `d` such that `(K,d)` is
totally bounded.  Examples are every finite group with any bi-invariant
metric (Hamming on `Sym(n)`, normalized rank on `GL_n(F_q)`, conjugacy-length
metrics), and `U(n)` with the operator norm or the normalized
Hilbert--Schmidt norm.  For a tuple `sigma in K^S` write

```text
Def_R(sigma)=max_(r in R) d(r(sigma),1).
```

**Chromatic certificates at `z`.** Each of the following is one:

- (CCC) a bounded-area infinite-chromatic commutator code, i.e. the
  hypotheses `(CCC1)-(CCC2)` of
  `infinite-chromatic-commutator-code-kills-mf-mark`, with constant
  `C=A_Delta+A_0`;
- (CDC) a bounded-area conjugacy-difference code, i.e. the hypotheses
  `(CDC1)-(CDC2)` of `bounded-area-conjugacy-difference-code-kills-mf-mark`,
  with `C=A`;
- (BHC) a bounded-area high-chromatic Carmichael section, i.e. the
  hypotheses `(BHC1)-(BHC3)` of `bounded-area-high-chromatic-conjugacy-collapse`
  for the word `w=z`, with `C=2L`.

**Theorem.**

(BI1) *Uniform bound.* If `z` carries a chromatic certificate with constant
`C`, then for every target `(K,d)` and every tuple `sigma in K^S`,

```text
d(z(sigma),1) <= C Def_R(sigma).
```

The bound is independent of `K`, of its size or dimension, and of which
target is used.

(BI2) *Local kill.* Let `(K_n,d_n)` be targets and `phi_n:Gamma->K_n` maps
with `d_n(phi_n(gh),phi_n(g)phi_n(h))->0` for all `g,h` with `g,h,gh` in a
fixed finite set `F`.  Here `F` contains `1`, the images of `S` and of
`S^(-1)`, and the images of all prefixes of every relator and of `z`.  Then
`d_n(phi_n(z),1)->0`.

(BI3) *Radicals.* `z` lies in the kernel of every homomorphism from `Gamma`
into a metric ultraproduct of targets.  So `z` lies in the weakly sofic,
sofic, hyperlinear and finite-field linear-sofic radicals of `Gamma`, as
well as in `Rad_MF(Gamma)`.

(BI4) *Non-approximability.* If `z!=1` in `Gamma`, then `Gamma` is not
weakly sofic in the sense of Glebsky--Rivera, and it is not hyperlinear.
Hence `non-weakly-sofic-group-exists` and `non-hyperlinear-group` both
follow.

(BI5) *Obstruction.* No finitely presented group with an approximation in
which `z` survives carries any chromatic certificate at `z`.  This rules out
all weakly sofic groups (in particular sofic, amenable, residually finite and
LEF groups), all hyperlinear groups and all finite-field linear-sofic groups.
For every such group and every nontrivial `z`, each of the three
certificate shapes must have unbounded area along any family whose
chromatic number diverges.

Derivation: `chromatic-code-bi-invariant-pigeonhole-proof`.

## Consequences

- **The operator norm plays no role.**  Nothing in the chromatic engine
  depends on the operator norm, on traces, or on matrices.  The only
  invariant used is that a bounded-cost relation stays close to `1` in a
  bi-invariant metric, whatever the conjugators.  The only step that uses the
  target is the pigeonhole, and that needs only finitely many colours at each
  scale.  So the belief recorded in
  `bounded-area-conjugacy-difference-code-kills-mf-mark` ("tailored to
  norm-matrix coronas") is false as a statement about strength: an MF
  conclusion from a chromatic code always comes with a weak-sofic and
  hyperlinear conclusion.
- **Hardness transfer for the Property-(T)-free manuscript.**  Any chromatic
  code route to `property-t-free-manuscript-results` proves two open roots
  along the way: Glebsky--Rivera Conjecture 4.5 (`non-weakly-sofic-group-exists`)
  and the existence of a non-hyperlinear group (`non-hyperlinear-group`).
  - The route `property-t-free-leavitt-via-chromatic-code` is one such route.
    Its leaf `binary-leavitt-bounded-area-chromatic-code` would settle both
    roots through the bridge routes `non-weakly-sofic-via-leavitt-chromatic-commutator-code`
    and `nonhyperlinear-via-leavitt-chromatic-commutator-code`.
  - The lifted-Thompson-`T` bounded-area code leaf (bounty 60, off main at
    commit `c4266f4b17`) is another.  It would make the central extension
    `T-bar` neither weakly sofic nor hyperlinear.
  - So each of these leaves is at least as hard as both open roots, well
    beyond the MF statement it was introduced to prove.
- **Where codes can live.**  A certificate can exist only around a mark that
  dies in every finite bi-invariant model.  The corpus's own finitely
  presented candidates must therefore be neither weakly sofic nor
  hyperlinear before a code can exist.
  For example, the corpus's non-MF group `E` is sofic (table rows 1-4 of
  `weak-soficity-survives-every-corpus-obstruction`).  Its marked word lies
  in `Rad_MF(E)` yet survives in sofic models, so by (BI5) no chromatic
  certificate of any of the three shapes exists at that mark.  This holds in
  every finitely presented group `Gamma` with a map onto `E` that sends the
  mark to `E`'s mark, because composing with `E`'s sofic models gives an
  approximation of `Gamma` in which the mark survives.
  - So `E`'s corona-invisibility is something no chromatic engine can
    reprove.
  - Every endpoint reached by a chromatic certificate is a group that is
    neither weakly sofic nor hyperlinear.
- **Correction to the weak-soficity survey.**  The survey
  `weak-soficity-survives-every-corpus-obstruction` concludes that only the
  word certificate is left.  This theorem gives a second, independent
  sufficient mechanism for non-weak-soficity, namely a bounded-area chromatic
  certificate around a nontrivial word.  It is no easier than the first: it
  is at least as hard as producing a non-hyperlinear group.
