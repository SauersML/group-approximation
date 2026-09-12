---
rg: 2
id: hs-literal-commutant-profile-rounding-proof
kind: route
title: Perturb a two-block representation to an irreducible tuple and keep its block projection
target: hs-literal-commutant-profile-rounding-is-false
requires: []
---

Notation is as in the target: `q : Gamma -> Q` onto a finite group,
`pi_1 : Q -> U(d)` nontrivial irreducible with `d >= 2`, `q(F) = Q`, `|F| >= 2`,
`D = 2d`, normalized trace `tau` and `||x||_2 = tau(x^* x)^(1/2)` on `M_D`.

**Step 1, the genuine representation.** Put

```text
pi = (pi_1 o q) (+) 1_d  on C^D,        p = I_d (+) 0.
```

`pi_1` is irreducible and nontrivial, so it has no trivial constituent. By
Schur's lemma, `pi(Gamma)' = C I_d (+) M_d`. The projection `p` is central in
this commutant, and it commutes with every `pi(g)`.

**Step 2, a gap for the conjugation action.** The map
`X -> pi(g) X pi(g)^*` is a unitary representation of `Gamma` on
`L^2(M_D, tau)`. It factors through `Q`, and its fixed space is `pi(Gamma)'`.
Let `E` be the orthogonal projection onto that fixed space. For `xi` orthogonal
to the fixed space, `(1/|Q|) sum_(g in Q) pi(g) xi = E xi = 0`, hence

```text
(1/|Q|) sum_(g in Q) ||pi(g)xi - xi||^2 = 2||xi||^2 - 2 Re <E xi, xi> = 2||xi||^2.
```

So `max_(g in Q) ||pi(g)xi - xi|| >= sqrt(2) ||xi||`. Since `q(F) = Q`, the
maximum is attained on `F`. Apply this to `xi = x - E(x)`. As `E(x)` is fixed,
`||pi(s) xi - xi||_2 = ||[pi(s), x]||_2`, and

```text
||x - E(x)||_2 <= (1/sqrt(2)) max_(s in F) ||[x, pi(s)]||_2.            (1)
```

**Step 3, commutators with `p`.** For a projection `p` and any `y`,

```text
[p, y] = p y (1-p) - (1-p) y p,
```

and the two terms are Hilbert--Schmidt orthogonal. Each is a corner of `y`, so
`||[p, y]||_2 <= ||y||_2`. Because `p` commutes with `E(x)`, (1) gives

```text
||[p, x]||_2 = ||[p, x - E(x)]||_2 <= (1/sqrt(2)) max_(s in F) ||[x, pi(s)]||_2.   (2)
```

**Step 4, an irreducible perturbation.** For `D >= 2`, tuples of at least two
unitaries with scalar common commutant are dense in the operator norm. The
proof is the lemma in `regular-quotient-perturbation-defeats-literal-poincare`,
section 2:
- perturb one unitary so that it has simple spectrum; its commutant is then
  diagonal in an eigenbasis;
- perturb a second unitary so that all its off-diagonal entries in that basis
  are nonzero, an open dense condition;
- a diagonal matrix commuting with it is scalar.

Choose `(U_s)_(s in F)` with `||U_s - pi(s)||_op < eta` and
`{U_s : s in F}' = C I`. Fix words `w_g` in `F` with `w_s = s` for `s in F`,
and set `theta(g) = w_g(U)`.

**Step 5, the estimates.**
- **(R1).** Telescoping gives `||theta(g) - pi(g)||_op <= |w_g| eta`. Hence
  `||theta(ss') - theta(s)theta(s')||_op <= (|w_(ss')| + 2) eta`, and `C_F` is
  the maximum of `|w_(ss')| + 2` over `s, s' in F`.
- **(R2).** `[p, pi(s)] = 0`, so
  `||[p, U_s]||_2 <= 2 ||U_s - pi(s)||_2 <= 2 eta`.
- **(R3).** For a contraction `x`,
  `||[x, pi(s)]||_2 <= ||[x, U_s]||_2 + 2 eta`, and (2) gives (R3).
- **(R4).** `theta(Gamma)' cap M_D` is contained in `{U_s}' = C I`. With
  `tau(p) = 1/2`, `||p||_2 = ||I - p||_2 = 1/sqrt(2)`.

**Step 6, the crux instance.** Take `eta = (sqrt(2)-1) delta / 2`. Then
`2 eta <= delta`, so `p` lies in `A(delta)` by (R2). For `x` in `A(delta)`,
(R3) gives `||[p,x]||_2 <= (delta + (sqrt(2)-1)delta)/sqrt(2) = delta`. The
defect is at most `C_F eta`. The distance bound (R4) does not depend on
`delta`. QED.

No property (T) of `Gamma` is used; the target merely records Kazhdan
instances. Only the finite quotient gap `sqrt(2)` enters, and it holds because
`F` covers `Q`.
