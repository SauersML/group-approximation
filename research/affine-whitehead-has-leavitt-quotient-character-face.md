---
rg: 2
id: affine-whitehead-has-leavitt-quotient-character-face
kind: claim
title: The affine Whitehead base has an infinite-kernel ordinary-Leavitt quotient character face
distinct_from:
  affine-whitehead-hyperfinite-stability-misses-canonical-mark: That identifies the strongest applicable stability theorem and its nonhyperfinite boundary; this proves that the stronger regular-or-finite-dimensional character dichotomy is actually false for the affine base.
  coefficient-central-affine-leavitt-envelope-is-morita-trivial: That computes a coefficient-algebra quotient; this passes it through the Steinberg and Whitehead quotients and extracts the resulting factorial character and normal-subgroup obstruction.
  leavitt-steinberg-hs-stable: That asks for normalized-HS stability of an ordinary Leavitt Steinberg cover; this proves that the same unresolved ordinary-Leavitt hyperlinearity face is already a quotient-character face of the affine construction.
---

**ESTABLISHED.**  Let

```text
R_A=L_A(k[C_aff]),
Gamma_A'=St_5(R_A)/normalClosure(W^4),
L=L_2(k),
Q=EL_5(M_3(L)).                                           (ALQ1)
```

Here `k` is the fixed finite splitting field of odd characteristic used by
the affine construction.  There is a surjection

```text
q:Gamma_A' -> Q times Q.                                  (ALQ2)
```

For either coordinate projection, the kernel of
`q_i:Gamma_A'->Q` is infinite and the quotient is infinite.  Moreover the
exchange-ring normal-subgroup theorem gives

```text
Qbar=Q/Z(Q)                                               (ALQ3)
```

as an infinite nonabelian simple group.  It is therefore ICC.  The pullback
of its regular character,

```text
chi(g)=1 if qbar_i(g)=1, and chi(g)=0 otherwise,           (ALQ4)
```

is an extremal factorial character of `Gamma_A'` which is neither the
regular character of `Gamma_A'` nor the character of a finite-dimensional
factor representation.

Consequently `Gamma_A'` does **not** have the regular-or-finite-dimensional
factor-character dichotomy.  It also fails the Margulis normal-subgroup
property in the strongest relevant way: it has an infinite normal subgroup
of infinite index.  Removing the finite inactive direct factor does not
repair this, because `(ALQ2)` already factors through the active direct
factor.

This does not misstate the more general Lavi--Levit conclusion.  Their
commutative-Noetherian theorem describes characters as induced from
finite-dimensional representations of suitable normal subgroups, rather
than asserting the regular-or-finite-dimensional dichotomy for every ring.
The character `(ALQ4)` is itself the character of
`Ind_(ker qbar_i)^(Gamma_A') 1`.  Thus even a purely formal transplantation
of that *shape* of conclusion would not imply hyperfiniteness: induction from
an infinite-index kernel produces the regular factor of the infinite quotient.

## The quotient

Put `S=k[C_aff]` and let `A` be the proper central active idempotent.  Since
the four relative Leavitt generators are supported by `A`, the idempotent
`1-A` is central in `R_A` and

```text
R_A=(1-A)S times A R_A A.                                 (ALQ5)
```

The Steinberg presentation preserves finite products, and `W` belongs to the
active factor.  Hence

```text
Gamma_A'=St_5((1-A)S) times
          (St_5(A R_A A)/normalClosure(W^4)).              (ALQ5a)
```

The first factor is finite because `(1-A)S` is a finite semisimple ring.
Thus the second factor is finite index, hyperlinearity of the two groups is
equivalent, and all quotient maps below already occur on that active factor.

Centralizing the finite coefficient head in the active factor gives the
surjective coefficient map computed in
`coefficient-central-affine-leavitt-envelope-is-morita-trivial`:

```text
A R_A A -> AS tensor_k L
          ~=M_3(L) times M_3(L).                          (ALQ6)
```

The Steinberg functor is surjective on surjective coefficient maps, and the
standard map from a Steinberg group onto its elementary group is surjective.
The signed Whitehead calculation `(FWA3)` says that the elementary image of
`W` has fourth power one in both factors.  Hence the map kills `W^4` and
descends to `(ALQ2)`.

Surjectivity onto the product shows directly that the kernel of either
coordinate map surjects onto the other copy of `Q`; it is therefore infinite.
This proof does not depend on whether the Steinberg kernel containing `W^4`
is finite, infinite, or central.

The Leavitt algebra `L` is purely infinite simple, so `M_3(L)` is a simple
exchange ring.  The normal-subgroup sandwich theorem for `EL_n` over an
exchange ring says that a normal subgroup of `Q`, modulo the central level,
has a two-sided coefficient ideal.  Simplicity leaves only levels zero and
one, proving simplicity of `Q/Z(Q)`.  Root subgroups make `Qbar` infinite.
An infinite nonabelian simple group is ICC, proving factoriality in `(ALQ4)`.

## Exact character-rigidity consequence

`Qbar` has property `(T)`: it is a quotient of the rank-five Steinberg group
over the finitely generated ring `M_3(L)`.  Thus it is infinite and
nonamenable.  If `Qbar` is hyperlinear, `(ALQ4)` is a Connes-embeddable,
nonhyperfinite factorial character of `Gamma_A'`.  Therefore a theorem saying

```text
every CE factorial character of Gamma_A' is hyperfinite or finite dimensional
                                                                  (ALQ7)
```

would already prove nonhyperlinearity of this ordinary Leavitt elementary
quotient.  That is the unresolved Hilbert--Schmidt Leavitt gate, not a
consequence of known higher-rank character rigidity.

This quotient face does not itself decide the **canonical** regular character
of `Gamma_A'`: the canonical character is faithful and remains in the regular
branch of every standard character theorem.  Normal-subgroup rigidity only
distinguishes its zero kernel from the kernel in `(ALQ4)`.  Connes
embeddability does not turn a faithful regular character into an amenable
one.  Relative property `(T)` does not do so either: even the canonical
representation of `Z^3 rtimes SL_3(Z)` is hyperlinear, has a diffuse root
algebra `L(Z^3)`, and the pair with `Z^3` has relative property `(T)`.

Thus the smallest missing statement on the canonical face remains a
nonhyperfinite marked lifting/correction theorem, equivalently the affine
root kernel-ideal estimate.  Neither normal-subgroup structure, finite-index
passage, the actual `W^4` quotient, nor relative property `(T)` supplies it.

## Primary-source boundary checked

- Lavi--Levit, arXiv:2007.15547, Theorem 1.1 and Corollary 1.3: the ring is
  required to be commutative Noetherian and the conclusion is induction from
  finite-dimensional data.
- Dogon--Vigdorovich, arXiv:2506.20843v2, Theorems 6.2 and 1.6: character
  rigidity controls hyperfinite stability or follows under additional
  stability hypotheses; it does not turn Connes embeddability of a regular
  factor into amenability.
- Ershov--Jaikin-Zapirain, arXiv:0809.4095, Theorem 6.2: Steinberg and
  elementary groups in rank at least three over finitely generated
  associative rings have property `(T)`; noncommutativity is allowed here.
- *On general linear groups over exchange rings*, Theorem 3: the sandwich
  classification used above is valid for `n>=3` and arbitrary exchange rings.

Proof: `affine-whitehead-leavitt-quotient-character-proof`.
