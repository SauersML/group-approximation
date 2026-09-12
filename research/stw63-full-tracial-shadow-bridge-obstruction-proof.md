---
rg: 2
id: stw63-full-tracial-shadow-bridge-obstruction-proof
kind: route
title: Push a proposed bridge into the trivial central sequence algebra of a full tracial shadow
target: stw63-full-tracial-shadow-forbids-joint-z-bridge
requires: []
artifacts:
  - research/artifacts/stw63-z-embedding-audit-2026-08-30.md
---

First prove the general assertion.  The homomorphism `theta:B->M` induces a
unital homomorphism

```text
Theta_omega:B_infinity -> M^omega,
[(b_n)]_(c_0) |-> [(theta(b_n))]_omega.                 (FTS3)
```

This is well defined because norm-null sequences are `2`-norm null.  Suppose
that `rho` as in `(FTS2)` exists and put `eta=Theta_omega rho`.  The range of
`eta` commutes with both constant copies `theta(phi(Z))` and
`theta(psi(Z))`, hence with the C-star algebra `S` they generate.

It in fact commutes with all of `M`.  Fix `z in Z`, represent `eta(z)` by a
uniformly bounded sequence `(x_n)` in `M`, and let `C=sup_n ||x_n||`.  For
`y in M`, Kaplansky density supplies elements `s in S`, uniformly bounded
with `y`, which approximate `y` in `2`-norm.  Since `[eta(z),s]=0`,

```text
||[x_n,y]||_2
 <= ||[x_n,s]||_2 + 2 C ||y-s||_2.
```

Take the `omega`-limit and then let `s` tend to `y` in `2`-norm.  Thus
`eta(Z) subset M' intersect M^omega=C1` by `(FTS1)`.  But `eta` is unital.
Its kernel is therefore a proper ideal of the simple algebra `Z`, so `eta`
is injective.  There is no injective homomorphism from the noncommutative
infinite-dimensional algebra `Z` into `C`.  This contradiction proves the
general obstruction.

Now take `F=Z*_(C)Z`.  Let `tau_Z` be the unique trace of `Z` and form the
tracial von Neumann free product

```text
(M,tau)=(pi_(tau_Z)(Z)'',tau_Z) *
        (pi_(tau_Z)(Z)'',tau_Z).                         (FTS4)
```

The universal property of the full C-star free product gives a unital
homomorphism `theta:F->M`, and the two canonical images weakly generate `M`.
Each factor in `(FTS4)` is diffuse.  Indeed, `tau_Z` is faithful and
extremal, so its GNS closure is a finite factor; it is infinite-dimensional
because the GNS representation is faithful, and an infinite-dimensional
finite factor cannot have a minimal projection.
Ueda, *Factoriality, type classification and fullness for free product von
Neumann algebras*, Adv. Math. 228 (2011), Theorem 3.7, proves in this diffuse
case that

```text
M' intersect M^omega=C1.
```

The general obstruction now rules out a joint bridge for `i_0,i_1`.

Finally, if the separable unital algebra `F` were `Z`-stable, the standard
central-sequence characterization of absorption would give a unital copy of
`Z` in `F_infinity intersect F'`.  That copy would commute with both
canonical ranges and hence would be a forbidden joint bridge.  Therefore
`F` is not `Z`-stable.

**Trust boundary.**  The only free-product input is Ueda's stated
central-sequence conclusion.  The argument does not infer failure of
approximate unitary equivalence from failure of the bridge; the canonical
orbit problem remains open.
