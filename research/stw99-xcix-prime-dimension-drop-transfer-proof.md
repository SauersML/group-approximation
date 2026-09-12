---
rg: 2
id: stw99-xcix-prime-dimension-drop-transfer-proof
kind: route
title: Transport image quotients of prime blocks using nuclear dimension one
target: stw99-xcix-prime-dimension-drop-defect-modulus
requires:
  - stw99-xciv-separable-zstability-iff-local-prime-dimension-drops
---

Every commutator of contractions has norm at most `2`, so `(DD1)` takes
values in `[0,2]`.  The established local prime dimension-drop criterion
says that, for a separable unital algebra `E`, `Z`-stability is equivalent to
the following statement: on every finite ambient set, every `I_k` has a
unital homomorphism into `E` which is arbitrarily central on `H_k`.  Scaling
the ambient finite set into the unit ball shows that this is exactly
`delta_(m,k)^dd(E)=0` for every `m,k`.  This proves `(DD2)`.

We prove the metric estimate without treating a near-selection as a map.
Fix contractions `x_1,...,x_m in B`, and choose contractions `a_i in A` with

```text
||x_i-a_i||<gamma.
```

Fix `k` and a unital homomorphism `psi:I_k->A`.  The map `psi` need not be
injective.  Put

```text
D=psi(I_k) subset A.
```

The algebra `D` is a separable quotient of the one-dimensional NCCW algebra
`I_k`, so

```text
dim_nuc(D)<=1.
```

Moreover `D subset_gamma B`.  Apply Christensen--Sinclair--Smith--White--
Winter, Theorem 6.10 in
[*Perturbations of nuclear C\*-algebras*](https://arxiv.org/abs/0910.4953),
with nuclear-dimension parameter `n=1`, to the finite set

```text
{1_D} union psi(H_k).
```

The theorem's constant is exactly

```text
eta=2(n+1)(2 gamma+gamma^2)(2+2 gamma+gamma^2)
   =4(2 gamma+gamma^2)(2+2 gamma+gamma^2),
```

and it gives an actual injective homomorphism `theta:D->B` satisfying

```text
||theta(psi(h))-psi(h)|| <= 20 sqrt(eta)       (h in H_k),
||theta(1_D)-1|| <= 20 sqrt(eta).                         (P1)
```

Here the theorem is applicable because `eta<1/210000`.  Indeed
`gamma<1/5670000<1/4` gives

```text
2 gamma+gamma^2 < (9/4)gamma,
2+2 gamma+gamma^2 < 3,
eta < 27 gamma < 1/210000.                              (P2)
```

The last estimate in `(P1)` is below `1`.  Since `theta(1_D)` is a projection
in the common unital algebra `B`, it must equal `1`; a proper subprojection
of `1` is exactly distance one from `1`.  Consequently

```text
phi=theta compose psi:I_k->B
```

is a genuine unital homomorphism.

For `h in H_k`, the commutator triangle inequality and `(P1)` give

```text
||[phi(h),x_i]||
 <= ||[psi(h),a_i]||
    +2||phi(h)-psi(h)||+2||x_i-a_i||
 <  ||[psi(h),a_i]||+40 sqrt(eta)+2 gamma.             (P3)
```

Take the maximum, then the infimum over `psi`, the supremum over the tuple,
and finally an arbitrarily small approximation to each infimum.  This gives

```text
delta_(m,k)^dd(B)
 <= delta_(m,k)^dd(A)+Lambda(gamma).                    (P4)
```

The same construction with an arbitrary source homomorphism also shows that
existence of a unital `I_k` map passes from `A` to `B`.  Hence, if one side
admits such maps for every `k`, both sides do.  Interchange `A` and `B` in
`(P4)`, using symmetry of Kadison--Kastler distance, to obtain the reverse
inequality.  Taking the supremum over `m,k` proves `(DD4)`.

If `A` is `Z`-stable, `(DD2)` makes `kappa_dd(A)=0`, which yields `(DD5)`.
Finally,

```text
(2 gamma+gamma^2)(2+2 gamma+gamma^2)=4 gamma+O(gamma^2),
```

so the leading term of `Lambda` is `160 sqrt(gamma)`, as asserted.

The only maps used above are the original homomorphism `psi` and the actual
embedding `theta` supplied by Theorem 6.10.  The elements `a_i` selected by
Kadison--Kastler closeness are never claimed to define a linear,
completely-positive, or multiplicative map.
