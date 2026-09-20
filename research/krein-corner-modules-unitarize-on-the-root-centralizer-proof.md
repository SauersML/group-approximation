---
rg: 2
id: krein-corner-modules-unitarize-on-the-root-centralizer-proof
kind: route
title: The centralizer preserves the rank-one odd line, so it acts there by form-preserving scalars, whatever the signature of the rest
target: krein-corner-modules-unitarize-on-the-root-centralizer
requires:
  - root-corner-star-reps-are-definite-krein-modules
  - leavitt-mf-null-root-corner-is-equivalent-to-the-goal
  - leavitt-st20-t-free-holes-hold-via-kazhdan
---

Notation is that of the target. Uses of the requirements:

- (U) uses only the definition of a definite-corner Krein module and (K2) of
  `root-corner-star-reps-are-definite-krein-modules`.
- (V) uses Steps 2 to 4 of `leavitt-mf-null-root-corner-is-equivalent-to-the-goal-proof` (the copy `M_18` inside the
  centralizer, the commutator chain, and `M_18` isomorphic to `Delta`, all without (T)), plus the Property (T)
  conclusion `Rad_MF(Delta) = Delta` of `leavitt-st20-t-free-holes-hold-via-kazhdan`. (V) is the only place (T) enters.

## Proof of (U)

Let `(M, sigma, xi)` be a definite-corner Krein module over `D`, and let `h` lie in `C = C_Gamma(z)`.

**Step 1. `h` preserves the odd line.** Since `h z = z h`, `sigma(h)` commutes with `sigma(P) = (1 - sigma(z))/2`. So
`sigma(h) sigma(P) M = sigma(P) sigma(h) M`, which is contained in `sigma(P) M = xi D` by (KM). As `xi` lies in
`sigma(P) M`, since `sigma(P) xi = xi`, we get `sigma(h) xi = xi u(h)` for some `u(h)` in `D`.

**Step 2. `u(h)` is unique and equals the corner coefficient.** Pairing with `xi` and using `D`-linearity of the form
in the second variable gives:

```text
[xi, sigma(h) xi] = [xi, xi u(h)] = [xi, xi] u(h) = u(h).
```

So `u(h)` is determined by `h`. By (K2), `[xi, sigma(g) xi] = rho(P g P)`, so `u(h) = rho(P h P)`.

**Step 3. Multiplicativity.** For `g, h` in `C`, `D`-linearity of `sigma(g)` gives:

```text
sigma(g h) xi = sigma(g)(xi u(h)) = (sigma(g) xi) u(h) = xi u(g) u(h).
```

By uniqueness, `u(g h) = u(g) u(h)`. Also `u(1) = [xi, xi] = 1`.

**Step 4. Unitarity.** The form is `Gamma`-invariant and conjugate-linear in the first variable, meaning
`[x d, y e] = d* [x, y] e`. So:

```text
u(h)* u(h) = u(h)* [xi, xi] u(h) = [xi u(h), xi u(h)] = [sigma(h) xi, sigma(h) xi] = [xi, xi] = 1.
```

By Step 3, `u(h) u(h^(-1)) = u(1) = 1`, so `u(h)` is invertible with inverse `u(h^(-1))`. A left inverse `u(h)*` of an
invertible element is its inverse, so `u(h) u(h)* = 1` too. Hence `u(h)` lies in `U(D)`, and `u` is a homomorphism
`C -> U(D)`.

**Step 5. The root.** `sigma(z) xi = -xi` by definition, so `u(z) = -1`.

**Step 6. The action on the odd line.** On `xi D` the form is `[xi d, xi e] = d* e`, which is positive. For `h` in
`C`, `sigma(h)(xi d) = xi u(h) d`. So `sigma|_C` on `xi D` is left multiplication by the unitary representation `u`.
Nothing in Steps 1 to 6 refers to the even part `sigma(Q) M`, so the signature of the form there is irrelevant.

The "equivalently" clause follows by applying Steps 1 to 6 to the universal module `M_rho` of (K2).

## Proof of (V)

Let `(M, sigma, xi)` be a definite-corner Krein module of `Delta` over `Q_k`, of any signature, and let `u` be as in
(U). `Q_k` is a unital C*-algebra, so (U) applies.

**Step 7. The copy of the whole group.** By Step 2 of `leavitt-mf-null-root-corner-is-equivalent-to-the-goal-proof`,
the relabelling `iota : St_18(R) -> Delta` onto the indices `J = {2, 4, 5, ..., 20}` has image `M_18` inside
`C_Delta(z)`. By its Step 4, `St_18(R)` is isomorphic to `Delta`, with no use of (T).

**Step 8. (T) kills the copy.** By `leavitt-st20-t-free-holes-hold-via-kazhdan`, `Rad_MF(Delta) = Delta`. So every
homomorphism `St_18(R) -> U(Q_k)` is trivial, and in particular `u o iota` is trivial. With `l = iota(1)` and
`m = iota(2)`, this gives `u(x_lm(1)) = 1`.

**Step 9. The commutator chain.** By Steps 2 and 3 of the equivalence proof, the elements `x_1l(q)`, `x_lm(1)`,
`x_1m(q)` and `x_m3(1)` lie in `C_Delta(z)`, and:

```text
x_1m(q) = [x_1l(q), x_lm(1)],        z = [x_1m(q), x_m3(1)].
```

Applying the homomorphism `u` gives `u(x_1m(q)) = [u(x_1l(q)), 1] = 1`, and then `u(z) = [1, u(x_m3(1))] = 1`.

**Step 10. Contradiction.** Step 5 gives `u(z) = -1`, and `-1 != 1` in `Q_k`, since `Q_k` is nonzero. So no such module
exists. By (K2), no unital star homomorphism `P_z C[Delta] P_z -> Q_k` exists either.

Both (R+) and (R-) of `root-corner-star-reps-are-definite-krein-modules` are special cases, since they only restrict
which modules are considered. The (R+) case covers countably generated Hilbert modules `X`. Given `(X, pi, V)` as in
(K3.4), let `xi = V(1)` and let `M` be the algebraic `Q_k`-span of `pi(Delta) xi`, with the restricted inner product.
Then `pi(P) M` lies in `pi(P) X = xi Q_k` and contains `xi Q_k`, so `M` is a definite-corner Krein module. (U) never
uses finite generation.

## Proof of (X1)-(X4)

**(X1).** Step 10 is a proof via (T) of the statement that (C2) says is not known to follow from (T). It covers the
two gaps (C2) names, countably generated `X` and indefinite forms.

**(X2).** Steps 1 to 10 have the form "take `rho`, unitarize, apply a unitary rigidity theorem". The unitarization is
(U), on `C_Delta(z)`. The rigidity theorem is `Rad_MF(M_18) = M_18`. No positivity (K3.3) is proved or used, so the
death step of (C3) fails for this member of the class. In (K4), `Gamma = D_inf = <z> * <y>` and `C_Gamma(z) = <z>`,
because in a free product a nontrivial element of a factor has centralizer inside that factor. There (U) gives only the
sign character of `<z>`, which carries no rigidity. So (K4) shows that positivity fails on `Gamma`, not that
centralizer unitarization fails.

**(X3).** By (U) together with Step 1 of the equivalence proof, `z in Rad_MF(C_Delta(z))` implies that no
definite-corner Krein module of either signature exists. So one T-free statement implies both (R+) and (R-). By (E) of
the equivalence node, that statement is T-freely equivalent to `property-t-free-leavitt-full-mf-radical`. Proving (R+)
T-freely therefore does not leave (R-) as a separate obstacle for a centralizer-based proof, and neither part is a
prerequisite that could fail while the goal holds.

**(X4).** By (X3), a T-free proof of the hole may consist of a T-free proof of `z in Rad_MF(C_Delta(z))`, which only
concerns homomorphisms `C_Delta(z) -> U(Q_k)`. It need not mention indefinite representations.
