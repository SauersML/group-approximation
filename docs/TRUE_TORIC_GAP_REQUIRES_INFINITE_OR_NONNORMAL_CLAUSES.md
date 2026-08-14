# A toric game gap requires infinite or nonnormal clauses

Status: proved reduction boundary; this is not a nonhyperlinear-group proof.

## 1. Why this audit matters

Watts--Helton--Klep associate to every finite nonlocal game a universal game
algebra

```text
U = C[G]
```

and call a game *torically determined* when it is determined by finitely many
relations

```text
h_i - 1,                 h_i = beta_i g_i,
```

where `g_i in G` and `beta_i` is a scalar phase.  If

```text
H = < h_i, h_i^* > <= U(U),
```

their Theorem 5.12 says that the game has a perfect commuting-operator
strategy exactly when

```text
H intersect C = {1}.
```

This is a powerful exact characterization.  It does not by itself turn a
perfect game into a marked group element.  The result below identifies one
case in which it *does* produce a canonical tracial corner, and shows that
this case can never carry a `qc=1>qa` separation.

Primary source:

- A. B. Watts, J. W. Helton, and I. Klep,
  [Noncommutative Nullstellensaetze and Perfect Games](https://arxiv.org/abs/2111.14928),
  especially Theorem 5.12.

## 2. Finite normalized clauses produce a central averaging corner

Let `G` be the universal game group and let `H` be the clause subgroup above.
Assume

1. `H` is finite;
2. `H intersect C = {1}`;
3. `g H g^(-1) = H` for every `g in G`.

Define

```text
p_H = |H|^(-1) sum_(h in H) h  in C[G].
```

Every element of `H` is a scalar multiple of a group unitary.  Since `H` is
a finite unitary group, the usual averaging calculation gives

```text
p_H^* = p_H,
p_H^2 = p_H,
h p_H = p_H                       (h in H).
```

The normalization assumption gives

```text
g p_H g^(-1) = p_H                (g in G),
```

so `p_H` is central in `L(G)`.

Let `tau_G` be the canonical group trace.  If a scalar-group monomial
`beta g` has `g=1`, it is a scalar.  The assumption
`H intersect C={1}` therefore says that the identity is the only member of
`H` whose group part is trivial.  Consequently

```text
tau_G(p_H) = 1/|H| > 0.
```

Thus the compression

```text
rho_H : C[G] -> p_H L(G),
rho_H(x) = p_H x,
```

is a unital star representation, where the unit of the corner is `p_H`, and
every clause satisfies

```text
rho_H(h_i) = p_H.
```

With the normalized corner trace, the GNS trace vector is therefore a
perfect strategy vector for the determining relations.

This is the exact canonical-trace feature missing from a general toric
subgroup-membership witness.

## 3. The corner is Connes embeddable

For a finite game, `G` is a finite direct product, over the players, of free
products of finite cyclic groups, one cyclic generator for each question.
It is residually finite and hence hyperlinear.  Therefore `L(G)` is Connes
embeddable, and so is the positive central corner `p_H L(G)`.

For completeness, in the two-player case a tracial perfect strategy in a
Connes-embeddable finite algebra is visibly in the closure of
finite-dimensional tensor-product strategies.  Embed the finite algebra in
a tracial matrix ultraproduct and lift Alice's and Bob's finitely many PVMs
to exact matrix PVMs

```text
E_(a,n)^x,    F_(b,n)^y in M_(d_n).
```

On the Hilbert--Schmidt space `M_(d_n)`, use left multiplication for Alice
and right multiplication for Bob:

```text
A_(a,n)^x(X) = E_(a,n)^x X,
B_(b,n)^y(X) = X F_(b,n)^y.
```

These are exact commuting PVMs.  Under
`M_d = C^d tensor conjugate(C^d)` this is an ordinary finite-dimensional
tensor-product strategy.  At the normalized identity vector its correlation
is

```text
<1, A_(a,n)^x B_(b,n)^y 1>
    = tr_(d_n)(E_(a,n)^x F_(b,n)^y),
```

which converges to the corner-trace correlation.  Hence the finite-dimensional
value has supremum one.

We have proved:

> **Finite-normal-clause theorem.**  Let `Gcal` be a finite two-player
> torically determined game, and let `H` be its clause subgroup.  If
> `H intersect C={1}`, `H` is finite, and `H` is normalized by the universal
> game group, then
> `omega_qa(Gcal)=omega_qc(Gcal)=1`.

Equivalently:

```text
omega_qc(Gcal)=1 > omega_qa(Gcal)
```

forces the clause subgroup to be infinite or genuinely nonnormal.

## 4. Why subgroup membership is not a quotient word

The normality hypothesis is not formal bookkeeping.  The exact toric
criterion gives

```text
phase notin H,
```

whereas a marked group quotient needs

```text
phase notin normal_closure(H).
```

These statements can be opposite.  Here is a finite abstract model.  Let

```text
Gtilde = C_2 times A_5,
```

write `b` for the central generator of `C_2`, choose an involution `a in A_5`,
and put

```text
H = < b a >.
```

Then `H intersect <b>={1}`.  But `b` lies in the normal closure of `H`.
Indeed, two distinct conjugates give a nontrivial element

```text
(b a)(b a^x) = a a^x in A_5.
```

The intersection of the normal closure with the simple group `A_5` is then
all of `A_5`; hence it contains `a`, and therefore also `b=(ba)a`.

So passing from `H` to its normal closure can destroy exactly the scalar
phase whose nonmembership supplied the perfect vector strategy.

## 5. Consequence for the hyperlinear program

The toric Nullstellensatz is not a broader ready-made replacement for the
perfect-LCS endpoint.

- If the clause subgroup is finite and normalized, the averaging projection
  gives a Connes-embeddable perfect trace and forces `qa=1`.
- If the clause subgroup is nonnormal, exact subgroup separation does not
  give a surviving word in a quotient.
- If the clause subgroup is infinite, its formal average is not a positive
  group-trace projection, so the canonical positive-density corner disappears.

Accordingly a useful toric compiler would need additional structure beyond
Theorem 5.12.  Two sufficient outputs would be:

1. a separately presented quotient or solution group with a nontrivial
   central finite-order phase, together with a dimension-independent decoder
   from its Hilbert--Schmidt microstates to near-perfect game strategies; or
2. an infinite-subgroup Hecke projection that exists in a finite canonical
   group-trace corner, is Connes-embeddability compatible, and retains the
   determining relations.

The first is the familiar perfect-LCS groupification gate.  The second is the
still-open Hecke-corner gate.  Exact toric subgroup membership alone supplies
neither one.

## 6. Audited endpoint

This audit does produce a clean structural restriction:

```text
toric qc/qa gap
    => clause subgroup infinite or nonnormal
    => no finite normalized averaging-corner shortcut.
```

The remaining viable game target is therefore not merely "a torically
determined game with a perfect commuting strategy."  It must come with a
robust normal groupification mechanism of the kind that is special to
solution groups, or with genuinely new infinite-subgroup corner machinery.
