# PSL2 dyadic Bruhat--Tits action: exact soficity fork — 2026-08-21

## Outcome

The action

```text
PSL_2(Z[1/2]) action PSL_2(Z[1/2])/PSL_2(Z)
```

is not currently settled by the available general theorems.  The new exact
result of this pass is that a positive answer forces flexible permutation
instability of `PSL_2(Z[1/2])`.  The proof uses the orbit charts themselves,
not the HNN extension and not the ascending-HNN telescope.

## Why the published positive criteria stop here

Gao--Kunnawalkam Elayavalli--Patchell, *Soficity for group actions on sets
and applications*, arXiv:2401.04945v3, prove soficity for coset actions with
locally finite stabilizer.  Their later paper with the author order
Gao--Patchell--Kunnawalkam Elayavalli, *Sofic actions on graphs*,
arXiv:2408.15470, Theorem 1.7 / 2.20, proves that a transitive graph action of
a sofic group is sofic when the vertex stabilizer is amenable, and
Proposition 1.2(4) says graph-action soficity implies soficity of the
underlying set action.

Here the vertex stabilizer is `PSL_2(Z)=C_2*C_3`, which is nonamenable and
not locally finite.  The stronger graph theorem therefore does not apply.
The same paper's free-group theorem does not apply to the acting group; using
it only on a vertex group does not provide compatible models across the
nonamenable index-three Iwahori edge.

Nor is the stabilizer separable in the acting group.  Congruence co-density
says that its image equals the whole image in every finite quotient.  Thus
the Chabauty/finite-index approximation criterion in Theorem 1.10 and the
finite-quotient coset construction cannot apply.

The splitting

```text
PSL_2(Z[1/2]) = PSL_2(Z) *_(Gamma_0(2)) PSL_2(Z)
```

also lies outside the proved ascending-HNN telescope: it has two vertex
embeddings joined by the Iwahori commensuration, rather than a nested
one-sided finite-index chain.  Păunescu's amalgamation theorem for sofic
actions assumes an amenable amalgam, whereas `Gamma_0(2) ~= Z*C_2` is
nonamenable.

## New quantitative reduction

For a co-dense pair `C<A` with a uniform spectral gap on exact finite
`A`-actions, a sofic atlas for `A/C` supplies one-hot labels for the base
coset.  If the underlying approximate permutations were close to an exact
finite action `rho`, the labels would be almost `rho(C)`-invariant.  Spectral
projection makes them close to the `rho(C)`-fixed space.  Co-density gives
`rho(C)=rho(A)`, so a fixed `h notin C` almost preserves the labels.  But
atlas covariance and injectivity force `h` to exchange the labels of `C` and
`h^(-1)C` on almost every good state.  This is a constant contradiction.

For the dyadic pair the uniform gap is Selberg's property `(tau)` on odd
congruence quotients.  Consequently:

```text
tree vertex action sofic
    => PSL_2(Z[1/2]) has noncorrectable permutation approximations
    => PSL_2(Z[1/2]) is not flexibly permutation-stable.
```

This is the precise current fork.  Nonsoficity of the action would only
close the Bernoulli countermodel to Iwahori stability; it would not prove
Hilbert--Schmidt stability or nonhyperlinearity.  Soficity would refute
flexible permutation stability and, by the already wired coset-Bernoulli
argument, refute the proposed Hilbert--Schmidt relative-commutant collapse.

## Upgrade: the fork controls the full HNN witness

There is an exact group-level identification

```text
<A,t | [t,C]=1> ~= ( *_(x in A/C) Z_x ) rtimes A
                 = Z wr^*_(A curvearrowright A/C) A.
```

Indeed, the free factor generator at `aC` maps to `ata^(-1)`; this is
well-defined because `t` centralizes `C`, and the two universal maps are
inverse.  Gao--Kunnawalkam Elayavalli--Patchell, Theorem 3.7, now implies

```text
A curvearrowright A/C sofic
    => <A,t | [t,C]=1> sofic.
```

This is stronger than the earlier commuting-lamp Bernoulli firewall.  It
retains all Britton/free-product moments of the stable letter.  Consequently
the action-soficity question directly controls the proposed nonhyperlinear
HNN group: proving that HNN nonhyperlinear would itself prove that the
dyadic vertex action is nonsofic.

It also gives the exact finite-coordinate enemy to any proposed
"full-canonical HNN" strengthening of Iwahori transfer.  Sofic microstates
of the HNN, followed by same-dimensional correction of its two
`PSL_2(Z)` vertex restrictions, retain canonical full-HNN moments and yield
a stable-letter centralizer of the first vertex but not the second.  The
graph projection of that unitary has trace `1/2`, so the failure is already
on two macroscopic blocks.  Thus neither canonical base trace nor canonical
full-HNN trace bypasses the fork.

## Primary sources checked

- David Gao, Srivatsav Kunnawalkam Elayavalli, Gregory Patchell,
  *Soficity for group actions on sets and applications*,
  arXiv:2401.04945v3 / Research in the Mathematical Sciences 12 (2025), 48.
- David Gao, Greg Patchell, Srivatsav Kunnawalkam Elayavalli,
  *Sofic actions on graphs*, arXiv:2408.15470, especially Proposition 1.2,
  Theorem 1.7, and Theorem 1.10.
- Alon Dogon and Itamar Vigdorovich, *Hyperlinearity, stability and
  asymptotic spectral gap of higher rank lattices*, arXiv:2506.20843v2,
  especially the Iwahori splitting and Question 1.4.
