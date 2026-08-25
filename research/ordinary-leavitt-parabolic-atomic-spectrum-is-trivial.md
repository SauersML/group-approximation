---
rg: 2
id: ordinary-leavitt-parabolic-atomic-spectrum-is-trivial
kind: claim
title: The atomic parabolic root spectrum of the ordinary Leavitt quotient is trivial
distinct_from:
  finite-root-algebra-forces-steinberg-triviality: that assumes one root algebra is finite dimensional and treats the binary Leavitt Steinberg cover; this allows an arbitrary atomic von Neumann root-column algebra and treats the full non-semisimple ordinary quotient used by the signed occurrence system.
  diffuse-active-spectrum-blocks-qualitative-collapse: that exhibits a diffuse exact tracial countermodel for an affine active module; this proves that diffuseness is the only possible location of a surviving ordinary-Leavitt root-column mark.
  ordinary-leavitt-quotient-fences-whitehead-active-floor: that shows a uniform signed-occurrence profile would make the ordinary quotient nonhyperlinear; this identifies the exact spectral summand on which such a profile still has to act.
---

**ESTABLISHED ATOMIC/DIFFUSE REDUCTION.**  Let `k` be the finite odd
splitting field of the affine construction, put

```text
L=L_2(k),                 R=M_3(L),
Q=EL_5(R),                H=EL_4(R)<=Q,
N=<x_i5(a):1<=i<=4, a in R>~=(R,+)^4.                 (OPA1)
```

Thus `H` is the upper-left elementary vertex and `N` is its abelian last-column
root module.  Let

```text
pi:Q -> U(M)
```

be an exact unitary representation in a finite tracial von Neumann algebra,
and let

```text
B=pi(N)'',              1=z_at+z_diff                 (OPA2)
```

be the canonical atomic/diffuse decomposition of the abelian von Neumann
algebra `B`.  Then

```text
pi(n) z_at=z_at                 for every n in N.      (OPA3)
```

In particular, for every fixed nonzero coefficient `a_0 in R`,

```text
||pi(x_15(a_0))-1||_2^2 <=4 tau(z_diff).               (OPA4)
```

If `B` is atomic, then `pi` is trivial.  This strictly extends the exact
finite-dimensional root-collapse theorem: the ambient finite tracial algebra
may be infinite dimensional, and only the root-column spectrum is assumed
atomic.

The reduction is sharp at the level of exact tracial representations.  In the
left regular representation, `B=L(N)` is diffuse and every nonidentity root
has canonical squared distance two from the identity.  Consequently no
universal finite-tracial argument can remove `z_diff`.

Applied to the quotient

```text
Gamma_A' -> Q=EL_5(M_3(L_2(k)))                        (OPA5)
```

inside the full signed Whitehead occurrence system, this identifies the exact
surviving HS gate.  Every tracial matrix-ultraproduct representation of `Q`
which keeps a canonical root nontrivial must put all of that nontrivial root
mass on the diffuse part of the **full parabolic coefficient vertex**.  Thus
the minimal promotion statement is not another Whitehead, Steinberg, finite
packet or root-kernel identity.  It is the matrix-coordinate assertion

```text
no diffuse N-spectrum in a tracial matrix ultraproduct can carry
the marked root.                                           (OPA6)
```

Together with `(OPA3)`, `(OPA6)` is exactly marked-root normalized-HS
collapse.  Since a noncentral elementary root normally generates the simple
central quotient of `Q`, it would make that quotient nonhyperlinear.  The
present theorem proves the whole atomic half of this assertion and makes no
claim about `(OPA6)`.

The next naive candidate is already fenced.  One cannot keep a bounded menu
of root characters at positive mass and hope that the full finite packet
forces an atom: `finite-tags-do-not-atomize-heisenberg-schrodinger-tower`
gives coherent finite Heisenberg windows whose individual character masses
are `p^(-N)` even after tensoring any fixed packet, while
`leavitt-character-mass-escapes-to-finer-characters` identifies the same
atom-to-diffuse escape in the branch multiplicity recurrence.  Any proof of
`(OPA6)` must therefore aggregate an unbounded character family with the
full coefficient-vertex returns, or supply a matrix-only anti-diffusion
estimate; bounded semisimple tags cannot bridge the atomic theorem to HS
collapse.

Proof: `ordinary-leavitt-parabolic-atomic-spectrum-proof`.
