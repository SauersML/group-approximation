---
rg: 2
id: approximate-to-asymptotic-central-path-proof
kind: route
title: Contract and concatenate successive approximately central transition unitaries
target: approximate-to-asymptotic-via-central-paths
requires: []
---

## Proof

Choose increasing finite sets `F_n` whose union is dense in the unit ball of
`A`, and numbers `epsilon_n -> 0`.  Apply the central path property to
`(F_n,epsilon_n)` and obtain `(G_n,delta_n)`.

Approximate unitary equivalence and a diagonal choice give unitaries `u_n`
such that `Ad(u_n)phi` is as close to `psi` as desired on

```text
F_n union G_1 union ... union G_n;
```

choose the errors small enough that both `u_n` and `u_(n+1)` have error less
than `delta_n/3` on `G_n`.  Set

```text
w_n = u_(n+1)^* u_n.
```

For `g in G_n`, conjugating the difference by `u_(n+1)` gives

```text
||w_n phi(g)w_n^* - phi(g)||
 <= ||u_n phi(g)u_n^* - psi(g)||
    + ||u_(n+1) phi(g)u_(n+1)^* - psi(g)||
 < 2 delta_n/3.
```

The left side equals `||[w_n,phi(g)]||`.  The central path property therefore
gives a path `v_n` from `w_n` to `1` which `epsilon_n`-commutes with
`phi(F_n)`.

Define a continuous unitary path on `[n,n+1]` by

```text
U(n+s)=u_(n+1)v_n(s),             0<=s<=1.
```

Its endpoints agree because `u_(n+1)v_n(0)=u_n` and
`u_(n+1)v_n(1)=u_(n+1)`, so the pieces concatenate.  For `f in F_n`,

```text
||Ad(U(n+s))(phi(f))-psi(f)||
 <= ||[v_n(s),phi(f)]||
    + ||Ad(u_(n+1))(phi(f))-psi(f)||,
```

and the right side tends to zero uniformly in `s`.  Density and contractivity
extend convergence to every `a in A`.  Extending the path constantly over an
initial compact interval gives the required path on `[0,infinity)`; no
condition on its initial unitary is needed.
