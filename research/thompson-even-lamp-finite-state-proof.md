---
rg: 2
id: thompson-even-lamp-finite-state-proof
kind: route
title: Freeze the finite character support and use Thompson simplicity
target: thompson-even-lamp-fp-finite-state-detector
requires:
  - augmentation-lamp-finite-presentation-criterion
  - thompson-v-has-no-nontrivial-fd-unitary-representation
artifacts:
  - research/artifacts/elementary-group-closures-2026-08-30.md
  - research/artifacts/finite-memory-self-hashing-non-mf-2026-08-23.md
---

The rational-tail action of Thompson's `V` is 2-transitive, and its point
stabilizer is finitely generated.  Since `V` is finitely presented,
`augmentation-lamp-finite-presentation-criterion` applies to

```text
I_X=ker(F_2^(X)->F_2),          Gamma_state=I_X rtimes V
```

and proves that `Gamma_state` is finitely presented.

Let `pi:Gamma_state->U(d)`.  The commuting involutions `pi(I_X)` are
simultaneously diagonalizable, so `C^d` is a direct sum of weight spaces for
a finite set `Omega` of characters `chi:I_X->F_2`.  Covariance makes `Omega`
a finite `V`-set.  Any action of the infinite simple group `V` on a finite
set is trivial: its kernel is normal, and an injective map from `V` to a
finite symmetric group is impossible.  Every `chi in Omega` is therefore
`V`-invariant.

It remains to compute the invariant characters.  A character of `I_X`
extends to a function `f:X->F_2`, unique modulo the constant function.  If
its class is invariant, then for every `g in V` there is `c(g) in F_2` with

```text
f(g^(-1)x)-f(x)=c(g)             for all x in X.        (1)
```

Applying `(1)` twice shows that `c:V->F_2` is a homomorphism.  Simplicity of
the nonabelian group `V` makes `c=0`; transitivity of the action then makes
`f` constant.  Thus every invariant character is trivial, every weight in
`Omega` is trivial, and `pi(I_X)=1`.

The representation consequently factors through `V`.  The established
finite-dimensional invisibility of Thompson's `V` makes that factor
trivial.  Hence every finite-dimensional unitary representation of
`Gamma_state` is trivial, proving the second assertion.
