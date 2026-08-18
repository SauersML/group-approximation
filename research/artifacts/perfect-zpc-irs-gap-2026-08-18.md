# 2026-08-18 — Perfect ZPC-IRS completeness with a quantum soundness gap

**Status:** the two hierarchy/undecidability statements in §§2–3 below are
proved from cited primary sources plus finite linear constraints; the final
readable-control freezing theorem in §5 is open.  No nonhyperlinear group is
claimed here.

This is a new reduction obtained by combining:

- Bowen--Chapman--Vidick, *The Aldous--Lyons Conjecture II: Undecidability*,
  arXiv:2501.00173, especially Definition 2.27 and Theorem 2.31
  (TailoredMIP*=RE);
- Aareyan Manzoor, *There is an equivalence relation whose von Neumann algebra
  is not Connes embeddable*, arXiv:2502.06697v2, especially Definition 3.4,
  Theorem 3.6 and Theorem 3.12.

The point is that Manzoor's computable IRS upper hierarchy can be restricted to
the **same Z-aligned / commute-along-edges (ZPC)** structural conditions used
in the perfect-completeness half of TailoredMIP.  The halting diagonalization
then forces a non-halting tailored instance whose restricted IRS value is
exactly one, while its finite-dimensional quantum value is below one half.

This is materially stronger than Manzoor's published Theorem 3.13, which only
extracts some game with `omega_IRS > omega*` and does not obtain perfect IRS
completeness.

---

## 1. The ZPC condition in stabilizer language

Manzoor's IRS strategy for a game is a p.m.p. action

```text
sigma : S union {J} -> Aut(X,mu)
```

with:

- `J` a free involution;
- each `u in S` an involution commuting with `J`;
- variables belonging to one question commuting.

Its stabilizer IRS is `H_x={g:g x=x}`.

For a tailored game, split its variables into readable and unreadable ones as
in Bowen--Chapman--Vidick.  Define a **ZPC-IRS strategy** to be an IRS strategy
which also obeys:

### Z alignment

For every readable variable `u`,

```text
u x is in {x,Jx}                 for a.e. x.              (Z1)
```

Because `u` commutes with `J`, this is constant on each two-point `J`-orbit.
In stabilizer language, using the freeness of `J`, (Z1) is exactly

```text
Pr[ u in H  or  Ju in H ] = 1.                            (Z2)
```

The two alternatives are disjoint: if both `u` and `Ju` fixed the same point,
then `J` would fix it.

This is the measurable-action analogue of Bowen--Chapman--Vidick Definition
2.27: in a finite signed permutation strategy a readable variable acts on
each signed pair either as the identity or as the sign flip.

### Commute along edges

For every sampled game edge `xy`, and every variables `u in S_x`,
`v in S_y`, require

```text
sigma(u)sigma(v)=sigma(v)sigma(u)   a.e.                  (Z3)
```

or equivalently

```text
Pr[[u,v] in H]=1.                                           (Z4)
```

A finite ZPC permutation strategy is therefore a ZPC-IRS strategy after
putting the uniform measure on its signed finite set.

Write `omega_ZIRS(G)` for the supremum of the game value over ZPC-IRS
strategies.

---

## 2. The ZPC-IRS value has computable decreasing upper bounds

**Theorem.** For every finite tailored game `G`, there is a computable sequence

```text
alpha_1^Z(G) >= alpha_2^Z(G) >= ... -> omega_ZIRS(G).       (H1)
```

### Proof

Use Manzoor's proof of Theorem 3.6.  Let

```text
F = F(S union {J})
```

and choose the exhausting finite sets `B_t` in his construction, enlarging the
first one once and for all so that it contains, in addition to the words needed
to evaluate the game,

```text
J, u, Ju                  for every readable u,
[u,v]                     for every edge xy, u in S_x, v in S_y.   (H2)
```

Manzoor's feasible set at level `t` is the computable polytope of invariant
random pseudo-subgroups of `B_t`, intersected with finitely many linear
conditions encoding the IRS-strategy axioms (`J` free, involutions,
commutation with `J`, and same-question commutation).

Add the ZPC equations

```text
sum_{A: u in A or Ju in A} pi(A) = 1,                    (H3)
sum_{A: [u,v] in A} pi(A) = 1.                           (H4)
```

These are finite rational linear equations in the coordinates `pi(A)`.  Hence
the new feasible set is still a computable polytope and maximizing the linear
game-value functional is a finite linear program.

The new constraints are restriction-compatible: once the words in (H2) are
present, they depend only on their membership indicators, and restriction from
`B_{t+1}` to `B_t` preserves them.  Thus the optima are decreasing.

Finally, the compactness argument in Manzoor's Theorem 3.6 is unchanged.
Choose maximizing pseudo-IRS measures at each level and a weak-* cluster
point.  Invariance and all original strategy equations survive because they
are closed.  Equations (H3)--(H4) also survive because the corresponding
cylinder events are clopen.  The limit is precisely a ZPC-IRS strategy.  The
game-value functional is continuous and depends on finitely many membership
coordinates, so the level optima converge to `omega_ZIRS(G)`.  QED.

Nothing non-effective entered this extension: it is literally Manzoor's LP
with finitely many additional `0/1` cylinder-event equations.

---

## 3. A perfect ZPC-IRS strategy separated from all finite-dimensional quantum strategies

**Theorem (perfect ZPC-IRS gap).** There is a finite tailored non-local game
`G` such that

```text
omega_ZIRS(G) = 1,
omega*(G) < 1/2.                                             (GAP)
```

Moreover the value `1` is attained by an actual ZPC-IRS strategy.

### Proof

TailoredMIP*=RE (Bowen--Chapman--Vidick, Theorem 2.31) effectively maps a
Turing machine `M` to a finite tailored game `G_M` satisfying:

```text
M halts     => G_M has a perfect finite ZPC permutation strategy;
M diverges  => omega*(G_M) < 1/2.                          (T1)
```

For every finite game, `MIP* subset RE` gives a computable increasing sequence
of lower bounds

```text
beta_t(G) -> omega*(G),                                    (T2)
```

as used by Manzoor in his Theorem 3.13.  Section 2 above gives a computable
decreasing sequence

```text
alpha_t^Z(G) -> omega_ZIRS(G).                             (T3)
```

Suppose, for contradiction, that every non-halting `M` obeyed

```text
omega_ZIRS(G_M) < 1.                                      (T4)
```

Then the halting problem would be decidable.  On input `M`, construct `G_M`
and dovetail the two sequences (T2)--(T3):

```text
accept  when beta_t(G_M) >= 1/2;
reject  when alpha_t^Z(G_M) < 1.                           (T5)
```

If `M` halts, (T1) supplies a perfect finite ZPC permutation strategy, hence a
ZPC-IRS strategy of value one.  Thus `omega_ZIRS(G_M)=1`, so the upper bounds
never drop below one; while `omega*(G_M)=1`, so the lower bounds eventually
cross `1/2`.  The algorithm accepts.

If `M` does not halt, (T1) gives `omega*(G_M)<1/2`, so the lower bounds never
cross `1/2`.  Under assumption (T4), the decreasing upper bounds eventually
drop below one, so the algorithm rejects.

This contradicts undecidability of halting.  Therefore some non-halting `M_0`
has

```text
omega_ZIRS(G_M0)=1.
```

The soundness half of (T1) gives `omega*(G_M0)<1/2`, proving (GAP).

Finally, the ZPC-IRS strategy space is a closed subset of the compact IRS
strategy space: it is cut out by finitely many clopen cylinder equations
(H3)--(H4).  The game value is continuous.  Therefore its supremum is
attained, so `G_M0` has an actual perfect ZPC-IRS strategy.  QED.

### Why this is a genuine strengthening

Manzoor's published diagonalization assumes a universal comparison between
`omega_IRS` and `omega*`, and extracts a strict gap somewhere.  The argument
above instead fixes the exact TailoredMIP family and asks only whether every
**non-halting** instance has restricted IRS value below one.  That weaker
hypothesis already decides halting.  So perfect IRS completeness is forced on
one soundness instance.

---

## 4. The readable variables are genuinely classical in a ZPC-IRS action

A useful elementary consequence of Z alignment is that all readable variables
commute globally in the p.m.p. action, not merely along game edges.

Indeed every readable `u` preserves each two-point `J`-orbit and acts on it as
`1` or `J`.  Since its choice is constant on that orbit, any two readable
variables commute pointwise.  Equivalently, on the quotient space

```text
Y = X / <J>
```

the readable variables are a global measurable bit field

```text
r : Y -> F_2^(S_R).                                       (R1)
```

For an unreadable variable `v` at a vertex `x`, the edge-commutation condition
says `v` preserves the readable bits belonging to `x` and to every neighboring
vertex of `x`.  What is **not** automatic is preservation of readable bits at
remote, nonadjacent vertices.

That distinction is exactly the remaining groupification barrier.

---

## 5. The one sharp missing theorem: freeze the readable control

Tailored games are controlled-linear: on an edge `xy`, the verifier first
reads the readable outcomes at `x,y`, and those bits select a finite system of
`F_2`-linear equations in all the local variables.  If one could freeze the
global readable field (R1) to one constant assignment without losing the
perfect unreadable strategy, the tailored game would reduce to an ordinary
LCS instance.

The precise open statement is:

> **Readable-control freezing.** If a finite tailored game has a perfect
> ZPC-IRS strategy, then there exists a global assignment `r` to all readable
> variables and a perfect commuting-operator strategy for the ordinary LCS
> obtained by substituting `r` into every controlled-linear constraint.

For the special game from §3, **every** frozen branch has quantum value `<1`:
if a fixed branch had a perfect finite-dimensional quantum strategy, combine
it with the deterministic readable answers `r`; this would be a perfect
quantum strategy for the original tailored game, contradicting
`omega*(G)<1/2`.

Thus readable-control freezing for the §3 game would give an LCS game with

```text
omega^co = 1,
omega* < 1.                                                 (LCS)
```

Manzoor explicitly recalls after Theorem 3.5 that such an LCS game yields a
nonhyperlinear group; this is also the `epsilon=0` endpoint highlighted by
Taller--Vidick, arXiv:2507.22444.

### Why freezing is not immediate

The global readable spectral atom is invariant under every readable operator,
but an unreadable operator at `x` is only known to commute with readable
operators at `x` and along edges incident to `x`.  It may move the values of
remote readable bits.  Therefore compressing to one **global** readable atom
can turn an unreadable involution into a leaking contraction rather than an
operator on that atom.

This is the exact obstruction.  No perfect-completeness amplification is left
to manufacture; no arbitrary BCS predicate needs to be linearized.  One must
show that the edge-local ZPC structure of the TailoredMIP instance is enough to
obtain one invariant readable fiber (or a phase-safe group substitute).

Potential outside tools for this step include:

- disintegration of representations over an abelian von Neumann algebra and
  groupoid-to-group rigidity;
- junction-tree / chordal marginal-gluing if the relevant readable dependency
  hypergraph of the TailoredMIP verifier has acyclic structure after
  compression;
- measurable cocycle cohomology: remote readable changes define an
  `F_2^(S_R)`-valued cocycle for unreadable generators, and killing that
  cocycle on a positive corner would make the global readable algebra
  invariant;
- amplify the quantum soundness gap first, so a compiler that loses a fixed
  amount of soundness is still sufficient.

The theorem in §3 makes these approaches target one fixed finite separated
object rather than a hypothetical future perfect-completeness game.
