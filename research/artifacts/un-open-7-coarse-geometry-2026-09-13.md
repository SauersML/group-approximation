# The coarse geometry of the UN ladder

Lane `un-open-7`, 2026-09-13. Plan: `research/artifacts/un-open-7-plan-2026-09-13.md` (f17de64477).
Everything new here is **unreviewed**. Nothing below decides a famous problem.

Throughout, `k` is a finite field, `𝒢` is Hausdorff, ample, minimal and effective with compact
infinite unit space, `R = A_k(𝒢)` is finitely generated as a ring, `n >= 3`,
`G = EL_n(R)` and `S = G/Z(G)`. By `steinberg-elementary-groups-are-simple-mod-centre`
(reviewed PASS, 171f0f7525) `S` is infinite and simple; by
`elementary-groups-over-fg-rings-have-property-t` it has property (T); by
`elementary-group-fg-from-fg-coefficient-ring` it is finitely generated.

## 1. RF-rigidity is free; only MF-rigidity is dynamical

**Lemma 1.1.** `G` is perfect for `n >= 3`.
*Proof.* For distinct `i, j, l` the Steinberg relation gives `e_ij(r) = [e_il(r), e_lj(1)]`, and
these generate. ∎

**Lemma 1.2.** `G` has no nontrivial finite quotient.
*Proof.* Let `φ: G -> F` with `F` finite and `K = ker φ`. Then `KZ/Z ⊴ S`, so by simplicity it is
trivial or all of `S`. If `KZ/Z = 1` then `K <= Z`, so `G/Z` is a quotient of the finite group
`G/K`, contradicting `S` infinite. So `KZ = G`, hence `G/K = KZ/K ≅ Z/(Z ∩ K)` is abelian; since
`G` is perfect (Lemma 1.1), `φ(G) = 1`. ∎

**Lemma 1.3 (folklore).** Every homomorphism from an infinite simple group `S` to a residually
finite group is trivial.
*Proof.* Let `φ: S -> H` with `H` residually finite. `ker φ` is trivial or `S`. If trivial, `S`
embeds in `H`, and residual finiteness passes to subgroups, so `S` is residually finite. Pick
`s ≠ 1`; some `ψ: S -> F` finite has `ψ(s) ≠ 1`, so `ker ψ ⊊ S` is normal, hence trivial, so
`S ↪ F` is finite — contradiction. ∎

**Corollary 1.4.** For every field `K` and every `d`, every homomorphism `S -> GL_d(K)` is trivial,
and `S` is not linear over any field.
*Proof.* The image is a finitely generated linear group, hence residually finite by Malcev's
theorem; apply Lemma 1.3. A faithful representation would be a nontrivial one. ∎

**The point.** Lemmas 1.2–1.3 use *only* simplicity and perfectness. They hold at **every** rung of
the ladder, paradox and measure alike. So the rigidity that the non-MF paper actually buys with the
dynamics is not rigidity against residually finite targets — that is free — but rigidity against the
strictly larger class of MF targets:

```text
RF  ⊊  LEF  ⊊  MF
 |       |       |
 |       |       +-- paradox side: every homomorphism to an MF group is trivial (tex Cor l.1016)
 |       +---------- measure side: S is LEF, hence MF; the identity is a faithful MF model
 +------------------ both sides: every homomorphism to an RF group is trivial (free, Lemma 1.3)
```

The whole UN dichotomy lives in the gap `RF ⊊ MF`. This is the cleanest statement I know of what
the two papers are really about, and it explains why the paper's theorems are stated for MF
targets rather than for finite or residually finite ones: any weaker target class makes the
theorem true for trivial reasons and blind to the dynamics.

**Uniform rigidity package.** Independently of the side, `S` has property (T), hence property FH
(Delorme–Guichardet) and property FA (Watatani): every action on a tree has a fixed point, and
every affine isometric action on a Hilbert space has a fixed point. With Corollary 1.4 and
Lemma 1.2: no finite quotients, no linear representations, no nontrivial tree actions. The
ladder is uniformly rigid; the dynamics is invisible to all of these invariants.

## 2. The coarse separation

The invariants of §1 do not separate the two sides. A coarse one does.

**Theorem 2.1.** Let `S` be a finitely generated, infinite, simple, LEF group. Then
1. `S` is not finitely presented;
2. `S` is not quasi-isometric to any finitely presented group;
3. `S` is not of type `F_2`, so it has no `K(S,1)` with finite 2-skeleton and no Dehn function.

*Proof.* (1) By `fp-upgrades-make-non-lef-and-non-lea-cheap` (Vershik–Gordon), a finitely
presented LEF group is residually finite. An infinite simple group is not residually finite
(Lemma 1.3 with `H = S`). So `S` is not finitely presented.
(2) Being of type `F_2`, i.e. finitely presented, is a quasi-isometry invariant of finitely
generated groups (Alonso). If `S` were quasi-isometric to a finitely presented group it would be
finitely presented, contradicting (1).
(3) Type `F_2` is finite presentability for a finitely generated group, and a Dehn function
requires a finite presentation. ∎

**Corollary 2.2 (coarse separation of the ladder).** Every measure-side rung — `S` with `R`
exactly matricial, so `S` LEF, for instance the Pestov witness
`EL_3(LC(X,F_q) ⋊ Z)/Z` of `infinite-simple-kazhdan-hyperlinear-group` — is quasi-isometric to no
finitely presented group whatsoever. The non-MF side does contain finitely presented examples: the
non-MF paper produces a finitely presented torsion-free Kazhdan group with no nontrivial
homomorphism to an MF group (abstract; via Hull's small cancellation theorem, tex l.1636). Hence
the two ends of the ladder are separated by a **quasi-isometry invariant**.

This is the geometric content the program was missing. Every separation recorded so far — no MF
quotient versus LEF, corona traces, rank functions, type semigroups — is operator-algebraic or
ring-theoretic, and none of those is known to be a coarse invariant. Finite presentability is one.
So the statement "these two families of infinite simple Kazhdan groups are genuinely different"
survives passage to any quasi-isometry, with no operator algebra used anywhere in the argument.

**Caveat, stated plainly.** Corollary 2.2 compares the measure side with a finitely presented
*non-MF-paper* group, not with a finitely presented group of the form `EL_n(A_k(𝒢))/Z`. Whether the
paradox side of the ladder itself contains a finitely presented rung is open; see §3. If it does
not, Corollary 2.2 still separates the measure side from the non-MF paper's own examples, but the
ladder's two ends would be coarsely indistinguishable by this invariant.

## 3. Is any paradox-side rung finitely presented?

`steinberg-finite-presentation-and-kazhdan-theorem` gives: for a finitely presented unital ring `R`
and `n >= 4`, `St_n(R)` is finitely presented, and it maps onto `EL_n(R)`. That node explicitly
declines to conclude anything about `EL_n(R)` without controlling the kernel. The kernel is
`K_2(n, R)`, so:

> **Open.** Is `K_2(n, L_k(1,d))` trivial (or at least finitely generated as a normal subgroup) for
> some `n >= 4` and `d >= 2`? A yes makes `EL_n(L_k(1,d))` finitely presented, which by Theorem 2.1
> immediately re-proves that it is not LEF, and completes the coarse separation *inside* the ladder.

Landed as `paradox-side-elementary-group-is-finitely-presented`, open, with Attempts.

Note the pleasing symmetry with `cohn-elementary-group-is-not-lef`, which runs exactly this
machine in the other direction: it uses finite presentation of `St_4(J)` to *refute* LEF for the
Cohn and Jacobson algebras, without needing `K_2` to vanish. So on those rings the paradox side is
already known to be non-LEF by a finite-presentation argument. What is missing is finite
presentation of the *group*, which is what a quasi-isometry invariant needs.

## 4. LEF growth: a quantitative invariant for the measure side

Theorem 2.1 says the measure side is uniformly far from finite presentations, but says nothing
about how measure-side rungs differ **from each other**. Nothing in the program currently does. A
natural candidate:

**Definition 4.1.** For a LEF group `S` with finite generating set `T`, let
`F_{S,T}(r) = min { |H| : H finite, and there is a map φ from the ball B_T(r) to H with
φ(xy) = φ(x)φ(y) whenever x, y, xy ∈ B_T(r), and φ injective on B_T(r) }`.
Changing `T` changes `r` by a bounded factor, so the growth class of `F_S` under `r ↦ Cr` is an
isomorphism invariant of `S`. This is the LEF analogue of residual finiteness growth.

**Upper bound (conditional, and the hypothesis is exactly what the Pestov construction supplies).**
Suppose the `r`-ball of `R_X = LC(X, F_q) ⋊ Z` is carried exactly by a Kakutani–Rokhlin tower model
`R_X ⊇ W_r -> M_{N(r)}(F_q)`, injective and multiplicative on `W_r`, with `N(r)` the tower height.
Then `EL_n` of that model is a finite group, and
`F_S(r) <= |EL_{n N(r)}(F_q)| <= q^{(n N(r))^2}`.
So the LEF growth of `S` is bounded by the **return-time function** of the subshift `X`. For a
Sturmian subshift of slope `α` the return times are governed by the continued fraction expansion of
`α`, so slopes of different Diophantine type give different upper bounds.

**The crux is the lower bound**, and it is genuinely open: it asks that no *smaller* finite group
model the `r`-ball, by any route, not only by towers. Landed as
`elementary-group-lef-growth-separates-subshifts`, open, with Attempts.

If the lower bound holds, one gets a continuum of pairwise non-isomorphic infinite simple Kazhdan
LEF groups indexed by Diophantine type — upgrading Pestov 9.1 from "such a group exists" to "the
dynamics is visible in the coarse geometry of the group". That is the sharpest thing this lane can
point at.

## 5. Status

- Lemmas 1.1–1.3, Corollary 1.4: standard arguments, written out; the content is the framing.
- Theorem 2.1, Corollary 2.2: **new as a statement about this program**, unreviewed. The
  ingredients (Vershik–Gordon via `fp-upgrades-make-non-lef-and-non-lea-cheap`; quasi-isometry
  invariance of type `F_2`) are classical and are cited, not reproved.
- §3 and §4: open claims with Attempts. No compute was run; no literature PDF was fetched this
  run, so Alonso and Malcev are cited from standard knowledge and are flagged as not re-read.
