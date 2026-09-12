---
rg: 2
id: four-cap-two-chart-mixer-has-finite-clifford-evaluator
kind: claim
title: The smallest marked two-chart cap mixer still has a finite Clifford evaluator
distinct_from:
  packet-retraction-evaluates-hecke-collision-atlas: that claim assumes a retraction onto the finite packet; the present mixer has no such retraction, but nevertheless has a finite-dimensional evaluation faithful on the packet.
  finite-edge-hnn-closures-cannot-finish-the-nonce-atlas: that claim gives the general residual-finiteness firewall for finite-edge HNN constructions; the present claim computes the exact four-cap two-chart cell and shows that even charging its cross-chart commutator by the common mark remains finite.
  four-cap-common-phase-forces-trivial-mark: that claim treats cap-independent coefficient words and proves universal mark collapse; the present construction retains the mark by mixing two selector charts, but proves that this first noncentral mixer is still matricial.
---

**ESTABLISHED.**  Let `E` be the two-qubit extraspecial Pauli group with
central involution `J`, and let

```text
A=<z_1,z_2> isomorphic to C_2^2,
K=E times A,
q=p_- tensor 1 in C[K],                                (TCM1)
```

where `p_-=(1-J)/2` is the nontrivial-central-character projection.  Thus

```text
q C[K] q isomorphic to M_4(C) tensor C[A]
              isomorphic to direct_sum_(A^*) M_4(C),   (TCM2)
```

the four summands being exactly the four cap-selector blocks of
`edgeful-or3-four-cap-walsh-packet`.

Adjoin one involution `t` and impose the relative presentation

```text
Gamma_2=<K,t |
  t^2=1,
  [t,e]=1                 (e in E),
  t z_1 t=z_1 J,
  [z_2,t z_2 t]=J>.                                      (TCM3)
```

Then all four of the tempting first-chord properties hold:

1. the natural map `K -> Gamma_2` is injective, so `q!=0`;
2. `J` is central and nontrivial in `Gamma_2`;
3. the first selector algebra `C[A]` and its second chart
   `t C[A] t` do not commute, since

   ```text
   [z_2,t z_2 t]=J!=1;                                  (TCM4)
   ```

4. there is no group retraction `Gamma_2 -> K` fixing `K`.

Nevertheless `Gamma_2` has a **sixteen-dimensional finite Clifford
evaluation faithful on `K`**.  Choose the faithful four-dimensional Pauli
representation

```text
rho_E:E -> U(4),             rho_E(J)=-I_4,
```

and on `W=C^2 tensor C^2` put

```text
Z_1=Z tensor I,
Z_2=I tensor Z,
T=X tensor H,                                         (TCM5)
```

where `X,Z` are the Pauli matrices and `H` is the Hadamard involution.  On
`C^4 tensor W` define

```text
rho(e)=rho_E(e) tensor I_4,
rho(z_i)=I_4 tensor Z_i,
rho(t)=I_4 tensor T.                                  (TCM6)
```

These matrices satisfy `(TCM3)`.  Moreover `rho|K` is faithful and the
image of all of `Gamma_2` is finite, being contained in the product of the
finite Pauli group with the finite two-qubit Clifford group.  In particular

```text
rho(q)=I_16,                                           (TCM7)
```

and the four cap atoms have nonzero finite rank.

This dimension is minimal for an evaluator faithful on the complete packet
corner: `(TCM2)` is a direct sum of four copies of `M_4(C)`, and a faithful
representation must contain a nonzero module of dimension at least four for
each summand.  Thus the construction is the smallest full four-cap
two-chart test in precisely the packet sense relevant here.

Thus destroying the literal packet retraction is strictly weaker than
destroying all packet-preserving finite evaluations.  Even the marked
cross-chart relation `(TCM4)` does not make the two-chart Fourier cell
load-bearing: every corner identity assembled in this cell still evaluates
in finite matrices.  A successful four-cap coefficient compiler must use a
non-Clifford additive multipath or a higher return whose incompatibility is
not contained in one finite projective two-chart groupoid.
