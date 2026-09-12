# 2026-08-24 -- Kervaire--Laudenbach cyclic-orbit kernel audit

Source: a user-supplied continuation of the 2026-08-17 Cairn audit.  The
source explicitly says that it does **not** prove Kervaire--Laudenbach.  This
audit confirms that boundary and integrates the new reduction and no-go
results into the graph.

## Headline

For an infinite nonabelian simple coefficient group `S`, a word
`w in S*<t>` of exponent sum `m>=1` determines a canonical quotient

    Q_w = N_m/<<w, alpha(w), ..., alpha^(m-1)(w)>>_(N_m),

where `N_m=ker(S*<t>->C_m)` and `alpha=Ad(t)|_(N_m)`.  The coefficient map is
injective exactly when `Q_w!=1`.  The new proof establishes that `Q_w` is
perfect and has no nontrivial finite quotient; it does not establish
`Q_w!=1`.

Thus the reduced conjecture has a sharper exact form, and finite quotient,
first homology, residual-finiteness and finite-dimensional linear searches
are structurally unable to witness the needed survivor.

## The cyclic-orbit calculation

Put `F=S*<t>`, let `pi_m:F->C_m` kill `S`, and put `N_m=ker(pi_m)`.  With
`z=t^m` and `S_i=t^iSt^(-i)`, Reidemeister--Schreier with transversal
`1,t,...,t^(m-1)` gives

    N_m = S_0 * ... * S_(m-1) * <z>.

Conjugation `alpha=Ad(t)` shifts the first `m-1` factors and satisfies

    alpha(S_(m-1))=zS_0z^(-1),   alpha(z)=z,   alpha^m=Ad(z).

Since `N_m` is normal in `F`, the ambient normal closure of `w` is the
`N_m`-normal closure of all `alpha^k(w)`.  The last identity makes every such
element `N_m`-conjugate to one of the first `m` orbit elements.  Hence

    <<w>>_F = <<w,alpha(w),...,alpha^(m-1)(w)>>_(N_m).

The closure lies in `N_m`, so quotienting `1->N_m->F->C_m->1` gives

    1 -> Q_w -> H_w -> C_m -> 1,

where `H_w=F/<<w>>_F`.

Because `S` is perfect, `N_m^ab=Z[z]`; the isomorphism is
`rho(x)=deg_t(x)/m`.  Each orbit relator has `rho(alpha^i(w))=1`, so the
relators kill the generator of the entire abelianization and `Q_w^ab=1`.

If `S->H_w` is not injective, simplicity kills all of `S`; the remaining
relation is `t^m=1`.  Since `H_w` also surjects onto `C_m`, it equals `C_m`
and `Q_w=1`.  Conversely `Q_w=1` gives `H_w=C_m`, whose coefficient map
kills `S`.  This proves the exact core equivalence.

For finite-quotient invisibility, compose any `Q_w->K`, with `K` finite,
with `N_m->Q_w`.  Its restriction to each `S_i` is either injective or
trivial by simplicity.  It cannot be injective because `S_i` is infinite, so
all coefficient factors die and the map factors through `N_m-><z>=Z`.
Every orbit relator maps to `z`, and those relators are trivial in `Q_w`, so
`z` dies too.  The map is trivial.

When `S` is finitely generated, so is `Q_w`.  Any nontrivial
finite-dimensional linear image would be a nontrivial finitely generated
linear group, hence residually finite by Malcev, and would have a nontrivial
finite quotient.  This contradicts the preceding paragraph.

## What changes in the graph

The old target “construct some action-compatible proper-normal-closure
quotient” was only a restatement of nontriviality after this canonical
quotient is named, so it has been removed.  Its concrete finite-nonabelian
proposal is retained as the invalidated route
`simple-kl-via-finite-quotient-certificate`.

The exact remaining assertion is now written directly on
`kl-holds-over-two-generator-simple-groups`:

    Q_w != 1 for every two-generator infinite simple S, m and w.

Finite simple groups lose nothing from the restriction because they are
hyperlinear and are already covered by
`kervaire-laudenbach-holds-for-hyperlinear`.

## External-source checks

### Osin--Thom

Denis Osin and Andreas Thom, *Normal generation and `l2`-Betti numbers of
groups*, Math. Ann. 355 (2013), 1331--1347,
[arXiv:1108.2411](https://arxiv.org/abs/1108.2411), was checked on
2026-08-24.  Its abstract states that the proposed bound
`beta_1^(2)<=normal rank-1` is for torsion-free groups and constructs, for
every `n>=2` and `epsilon>0`, a simple torsion group with
`beta_1^(2)>=n-1-epsilon`.  Since every nonidentity element normally
generates a simple group, these examples have normal rank one.  They rule out
the proposed torsion-insensitive numerical replacement.

### Chen

Lvzhou Chen, *The Kervaire conjecture and the minimal complexity of
surfaces*, [author PDF](https://lvzhouchen.github.io/papers/kervaire.pdf), was
read directly on 2026-08-24.  The relevant items are:

- Definition 5.1: relative `n`-RF, and for trivial edge subgroup equivalence
  with order at least `n`; at `n=infinity`, free relative to the edge group;
- Theorem 5.3 and Corollary 5.4: the local HNN estimate and injectivity under
  the `infinity`-RF/RTF hypotheses;
- Corollary 6.5: the unconditional coefficient `1/2` for a unimodular word in
  `A*Z`, strengthened to `1-1/n` when every nonidentity element of `A` has
  order at least `n`;
- Question 7.1: extension of the main estimate beyond the current exponent
  and relative-freeness setup is left open.

Here every orbit relator is individually unimodular in
`N_m=(*S_i)*<z>`.  A minimal identity with `k` conjugates yields a punctured
sphere with `-chi=k-1` and degree `k`.  The unconditional estimate gives only
`k-1>=k/2`, compatible with every `k>=2`; coefficient one gives the needed
contradiction `k-1>=k`.  This rules out use of the bare one-half estimate as
the final numerical step.  It does not claim a multi-relator extension of
Chen's theorem for `Q_w`.

## Trust boundary

The cyclic-orbit theorem is proved in full in this artifact and in
`kl-cyclic-orbit-perfect-kernel-proof`; it uses no assertion of the open
nontriviality.  The Osin--Thom and Chen items are literature imports, isolated
in their own citation/audit routes.  No node says “therefore `Q_w!=1`”.
