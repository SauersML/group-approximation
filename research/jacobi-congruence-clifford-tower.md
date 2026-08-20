---
rg: 2
id: jacobi-congruence-clifford-tower
kind: claim
title: A finitely presented Jacobi congruence tower realizes the binary Clifford tape with fixed word templates
distinct_from:
  self-similar-clifford-quantum-expander-tape: that states the complete expander-tape interface; this isolates the remaining algebraic construction after relative property (T) supplies its spectral gap.
---

Construct a finitely presented group `Gamma` containing a Heisenberg-type
normal subgroup and fixed words `S`, together with nested finite quotients
`Gamma_n` and projective representations

```text
pi_n: Gamma -> PU((C^2)^(tensor r_n)),   r_n -> infinity,
```

such that:

1. the Heisenberg image acts by the irreducible binary Schrodinger
   representation and has local central signs
   `J_n=t^n J_0 t^(-n)` transported by one compressor word;
2. the adjoint actions of the fixed words `S` normalize the Pauli group, so
   they are Clifford checks on every prefix;
3. the level shift and the inclusion of one new Pauli cell are represented by
   fixed group words with derivations of polynomial cost in the level;
4. the selector-controlled affine commutators of the Schur rank gate use the
   same central sign and commute with the old prefix as required; and
5. `(Gamma,N)` has a fixed relative Kazhdan pair for the Heisenberg normal
   subgroup `N` (or another fixed normal subgroup acting irreducibly in every
   `pi_n`).

By `relative-t-heisenberg-adjoint-quantum-expansion`, item 5 turns `S` into
uniform quantum expanders automatically. Items 1--4 then imply
`self-similar-clifford-quantum-expander-tape`.

## Attempts

- **Truncated-polynomial tower: finite-level algebra solved.**
  `truncated-polynomial-binary-weyl-expander-tower` uses `F_2[u]/(u^n)` and
  the top-coefficient Frobenius functional. It gives exact `2^n`-dimensional
  Weyl systems, a symplectic inclusion adding one qubit, and fixed
  relative-Kazhdan expander words. The obstruction is now compatibility:
  `(a,b)|->(ua,b)` is not a ring homomorphism, the linear action does not
  preserve every embedded prefix, and the top-coefficient cocycle varies
  with `n`. The sign variation alone is repairable by
  `conjugate-local-signs-preserve-marked-carrier`: a ring-valued center and a
  compressor taking `z(c)` to `z(uc)` turn the top-coefficient signs into
  conjugates. The unresolved part is making that compressor and the fixed
  linear expander action coexist on the nested inclusions.
- **Laurent/unitary repair.** A coefficient-of-identity pairing over
  `F_2[t,t^(-1)]` has a level-independent formula and suggests replacing the
  symplectic group by a unitary group for `t* = t^(-1)`. No nested finite
  quotients and compatible one-cell embeddings carrying all of the required
  action have yet been exhibited.
- **Two-chart repair. Active.** A module-linear symplectic inclusion is
  impossible by `no-linear-symplectic-splitting-of-truncated-weyl-levels`.
  However, `truncated-weyl-two-chart-boundary` gives two symplectic charts
  which overlap on `n-1` qubits and differ by only one transverse qubit;
  upper and lower elementary maps preserve opposite charts and incur the
  explicit drift `r|->ur`. This reduces the compatibility problem to
  `two-chart-jacobi-action-holonomy` rather than an unbounded prefix defect.
