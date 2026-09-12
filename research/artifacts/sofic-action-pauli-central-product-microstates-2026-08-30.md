# Sofic action charts give marked microstates for the common-center Pauli lamp

Date: 2026-08-30

Status: proved below.  This is a bounded obstruction for the
infinite-character/Pauli-seed route, not a proof or refutation of the full
`infinite-character-actor-word-energy-interface`.

## 1. Result

Let a countable group `A` act on a countable set `X`.  Write

```text
V_X = direct_sum_X F_2
```

and define the binary Pauli central product

```text
P_X = V_X x V_X x F_2                                      (P1)
```

with multiplication

```text
(u,v,e)(u',v',e')
  = (u+u', v+v', e+e'+<v,u'>),                            (P2)
```

where every scalar is in `F_2` and

```text
<v,u'> = sum_(x in X) v_x u'_x.
```

Put

```text
J=(0,0,1),       X(u)=(u,0,0),       Z(v)=(0,v,0).        (P3)
```

Then

```text
[X(u),Z(v)] = J^(<v,u>).                                  (P4)
```

The coordinate action of `A` preserves the pairing and hence acts on
`P_X`, fixing `J`.

> **Theorem (chartwise replicated-center construction).**  If `A` is sofic
> and the set action `A action X` is sofic, then
>
> ```text
> P_X semidirect A                                        (P5)
> ```
>
> is sofic.  Its sofic approximations can be chosen so that `J` has Hamming
> distance exactly `1` from the identity at every stage.

The point not covered by the ordinary restricted-wreath argument is that
all finite site packets share the same `J`.  The construction below copies
`J` once in every action-chart fibre and maps the source mark to the diagonal
tuple of those copies.  Thus a covariance failure on an `eta`-fraction of
charts costs only `O(eta)` in normalized Hamming distance, while the diagonal
mark remains fixed-point-free everywhere.

## 2. The finite Pauli packets

For a finite label set `L`, formula `(P2)` defines a finite group `P_L`.
Associativity follows from bilinearity of `(v,u') |-> <v,u'>`.  The triple in
`(P1)` is a unique normal form, so `J` is nontrivial.  Moreover, if

```text
j:E -> L
```

is injective on a finite set `E subset X`, the linear push-forward

```text
j_* : F_2^(E) -> F_2^(L),
```

preserves the pairing:

```text
<j_*v,j_*u> = <v,u>.                                     (P6)
```

Consequently

```text
(u,v,e) |-> (j_*u,j_*v,e)                                (P7)
```

is an exact homomorphism on every finite Pauli packet supported in `E`.
Injectivity of `j` also makes `(P7)` injective on that packet.

If `j` is not injective, `(P7)` need not be multiplicative: cross terms can
appear when labels collide.  This is harmless below because a sofic action
chart is injective on any prescribed finite site window outside a set of
arbitrarily small density.

## 3. Input supplied by a sofic set action

Use the liftable-label characterization recorded in
`gkp-sofic-action-is-liftable-hamming-chart-family`.  For a finite actor
window `K subset A`, finite site window `E subset X`, and `eta>0`, it gives a
finite carrier `Omega`, permutations

```text
sigma_a in Sym(Omega),        a in K,
```

and label maps

```text
ell_x : Omega -> N,           x in E,                    (P8)
```

into one label set `N`, such that:

1. the `sigma_a` multiplication table is correct off a set of density
   `eta` for every required product in `K`;
2. for `x!=y` in `E`,

   ```text
   Pr_omega[ell_x(omega)=ell_y(omega)] < eta;             (P9)
   ```

3. whenever `a,x,ax` occur in the chosen windows,

   ```text
   Pr_omega[
     ell_(ax)(sigma_a omega) != ell_x(omega)
   ] < eta.                                               (P10)
   ```

After taking a union bound, the map

```text
x |-> ell_x(omega)                                       (P11)
```

is injective on all of `E` outside a set of density at most
`binom(|E|,2)eta`.  All required instances of `(P10)` hold simultaneously
outside a set of density at most `|K||E|eta`.

The action approximation need not separate nonidentity elements of `A`.
Choose independently an `(K,eta)` sofic group approximation

```text
tau_a in Sym(Lambda)
```

and replace the carrier by

```text
D=Omega x Lambda,
hat_sigma_a(omega,lambda)
  =(sigma_a omega,tau_a lambda).                          (P12)
```

Pull the labels back from `Omega`.  Equations `(P9)` and `(P10)` keep the
same densities, while every prescribed `a!=1` moves at least a
`1-eta` fraction of `D` because `tau_a` does.

## 4. Replicate the center over the chart carrier

Let `L` be the finite set of label values appearing in `(P8)` for the
chosen `E` and `Omega`.  Form the finite wreath group

```text
Q = P_L^D semidirect Sym(D).                              (P13)
```

We use the usual action of `Sym(D)` on base functions,

```text
(pi.f)(d)=f(pi^(-1)d).
```

Give `Q` its faithful imprimitive permutation action on `P_L x D`: the base
copy at `d` acts by the left-regular action on the fibre over `d`, and
`Sym(D)` permutes the fibres.  Two base functions that disagree on a
`theta`-fraction of `D` have normalized Hamming distance exactly `theta`,
because unequal left translations agree nowhere in their fibre.

For a Pauli word `p=(u,v,e)` supported in `E`, define `f_p in P_L^D` by

```text
f_p(omega,lambda)
  = ( sum_x u_x delta_(ell_x(omega)),
      sum_x v_x delta_(ell_x(omega)),
      e ).                                                (P14)
```

The last coordinate is repeated at **every** `d in D`.  In particular,

```text
f_J(d)=J_L             for every d.                       (P15)
```

For a finite source window in `P_X semidirect A`, enlarge `K` and `E` so
that they contain all actor components, all supports, all supports moved by
the actor components, and all products needed to test multiplication.  Put

```text
Theta(p,a)=(f_p,hat_sigma_a) in Q.                         (P16)
```

At a carrier `d` where `(P11)` is injective, `(P6)` says that the Pauli
multiplication table is exact.  At a carrier `d` where all required
instances of `(P10)` hold, the convention above gives the pointwise identity

```text
(hat_sigma_a.f_p)(d) = f_(a.p)(d).                        (P17)
```

Thus, for every prescribed pair of source elements, the two sides of its
multiplication equation under `Theta` agree on every fibre except:

- a fibre where a required actor product fails;
- a fibre with a collision among labels from `E`; or
- a fibre where one of the required covariance equations fails.

The normalized Hamming defect is therefore at most

```text
C_(K,E) eta,                                              (P18)
```

where, for example, one may take a constant obtained by adding
`2+binom(|E|,2)+|K||E|` once for each of the finitely many tested products;
the initial `2` accounts for the two actor permutation approximations in
`(P12)`.
Since `eta` is arbitrary, `(P16)` is asymptotically multiplicative.

It remains to check separation.  If `(p,a)` has `a!=1`, its permutation of
the fibres moves at least `1-eta` of them by `(P12)`.  If `a=1` and `p!=1`,
then on every carrier where `(P11)` is injective on the support of `p`, the
normal form in `P_L` makes `f_p(d)` nonidentity.  Its left-regular action
moves the entire fibre.  Finally, when `p=J`, equation `(P15)` shows that it
moves every point of every fibre, with no error at all.  This proves the
theorem.

The proof is finitary: for a requested finite group window one chooses the
corresponding `K,E`, then makes `eta` small compared with the displayed
union-bound constant.  No ultraproduct lifting or closure of soficity under
quotients is being assumed.

## 5. The two-point Pauli seed has a marked sofic quotient

Suppose now that the action is transitive, choose distinct `p,q in X`, and
put

```text
m_0=delta_p+delta_q in V_X.                               (P19)
```

Consider the bare Pauli-seed extension used in
`infinite-character-actor-kills-fd-mark` and
`sl3-codense-coset-lamp-recursive-host`:

```text
G_seed=<V_X semidirect A,z,J |
        z^2=J^2=1, J central, [m_0,z]=J>,                 (P20)
```

where `(P20)` abbreviates the semidirect relations and imposes no additional
relations on `z` beyond the displayed ones.  There is a surjection

```text
G_seed -> P_X semidirect A                               (P21)
```

given by

```text
u |-> X(u),        a |-> a,
z |-> Z(delta_p),  J |-> J.                              (P22)
```

Indeed `(P4)` and `(P19)` give

```text
[X(m_0),Z(delta_p)]=J.                                   (P23)
```

Transitivity makes the conjugates of `Z(delta_p)` all the `Z(delta_x)`, so
the image contains both Pauli coordinates and `(P21)` is onto.  The normal
form `(P1)` proves that the image of `J` is nontrivial.

Consequently, if `A` and `A action X` are sofic, `G_seed` has a sofic
quotient in which `J` survives.  Pulling back the sofic approximations of
that quotient gives matrix/permutation microstates for every fixed finite
word and relational window of `G_seed`, with

```text
d_H(J,1)=1,
||J-I||_2=sqrt(2)                                        (P24)
```

after permutation linearization.  If the additional aperiodicity hypothesis

```text
chi(m_0)=-1  ==>  |A chi|=infinity                        (P24a)
```

holds -- as it does in the `SL_3` application below --
`infinite-character-actor-kills-fd-mark` says that every **exact**
finite-dimensional representation of `G_seed` kills `J`.  There is no
conflict: the maps in `(P16)` are asymptotic representations, not
homomorphisms of the whole infinite group into a fixed finite target.
Without `(P24a)`, exact finite-dimensional representations need not kill
`J`; the sofic permanence theorem itself assumes no aperiodicity.

## 6. Concrete consequence for the dyadic `SL_3` lamp route

Take

```text
A=SL_3(Z[1/2]),       C=SL_3(Z),       X=A/C.             (P25)
```

The group `A` is residually finite and hence sofic.  Therefore

```text
A action X sofic
  ==> the two-point seed extension has marked sofic
      microstates satisfying (P24).                       (P26)
```

In particular, any proposed normalized-Hilbert--Schmidt theorem which uses
only the defect on a fixed finite window of the bare semidirect/seed
relations to force `J` close to the identity would imply that the dyadic
building action in `(P25)` is **not** sofic.  The same conclusion holds for
a pointwise asymptotic statement over an enumerated recursive presentation,
by a diagonal choice of the pulled-back sofic approximations.  This is the
precise analogue, for the Pauli-seed route, of
`sl3-regular-double-collapse-forces-nonsofic-vertex-action`.

This is a real increase in the burden carried by the analytic interface.
The graph currently records only the exact-action firewall
`sl3-dyadic-building-action-soficity-forces-p-instability`; it explicitly
does not decide whether `(P25)` is a sofic action.  Thus a Pauli-seed
`J`-collapse for this host would also settle that separate open dynamical
question.

## 7. Scope and failed-space audit

1. **No direct halo citation.**  The common-center packet is not a standard
   set halo: local groups on two disjoint nonempty site sets intersect in
   `<J>`, whereas the halo intersection axiom has trivial empty-set group.
   The proof above replaces the missing halo step; it does not claim that
   Alekseev--Bradford already proves the theorem.

2. **No conflict with lamp-chart recovery.**  The claims
   `single-lamps-recover-set-action` and `lamp-charts-recover-set-action`
   run in the converse direction: suitable lamp charts force the underlying
   set action to be sofic.  Here soficity of that set action is an explicit
   hypothesis and its charts are exactly the input used in `(P8)`.

3. **No conflict with the exact-atlas firewall.**  The finite targets in
   `(P13)` use almost-multiplicative actor permutations.  They are not exact
   finite `A`-actions and hence do not contradict
   `sl3-prime-coset-action-exact-atlas-firewall`.

4. **The moving-character leak is expected.**  The construction produces
   the kind of asymptotic models on which
   `finite-covariance-energy-sees-only-character-restrictions` and
   `pointwise-lamp-covariance-has-half-mass-leak` obstruct a fine PVM
   transport bound.  It does not select a globally covariant spectral lift.

5. **Stronger than the regular-action falsifier, but only conditionally.**
   `sofic-actor-refutes-lamp-character-transport` supplies a marked
   microstate obstruction for its special regular/Tarski setup.  The
   chartwise proof above works for every sofic set action of a sofic actor
   and handles the common-center Pauli quotient explicitly.  It says nothing
   when either soficity hypothesis fails or is unknown.

6. **The original interface is not refuted.**  The claim
   `infinite-character-actor-word-energy-interface` is allowed to choose a
   nonsofic action, a nonsofic actor, or additional finite-presentation
   relations not respected by `(P21)`.  The theorem only rules out a bare
   Pauli packet when both soficity hypotheses hold.  A viable packet must
   therefore escape through at least one of:

   ```text
   failure of actor or site-action soficity;
   extra controller/holonomy relations destroyed by (P21);
   a hypothesis using more than bare presentation defect and J-separation.
   ```

## 8. Suggested Cairn graph impact

The proof supplies the reusable established claim

```text
sofic-action-gives-marked-pauli-central-product-microstates
```

and suggests the separate conditional arithmetic consequence

```text
sl3-pauli-seed-collapse-forces-nonsofic-vertex-action.
```

It should not mark `infinite-character-actor-word-energy-interface` false or
close `sl3-codense-lamp-higman-route`.  Its graph role is a falsification
edge: any proof of the latter route must identify where it proves the
nonsoficity alternative in `(P26)` or where its additional relations prevent
the quotient `(P21)`.

## References inside the repository

- `gkp-sofic-action-is-liftable-hamming-chart-family` for `(P8)--(P10)`;
- `gkp-wreath-permanence-theorem` for the commuting-lamp comparison;
- `infinite-character-actor-kills-fd-mark` for the exact finite-dimensional
  collapse which `(P24)` does not contradict;
- `sl3-codense-coset-lamp-recursive-host` for the packet `(P19)--(P20)`;
- `lamp-charts-recover-set-action` for the converse chart-extraction
  firewall;
- `sofic-halo-products-preserve-hyperlinearity` and its artifact for the
  ordinary halo boundary;
- `sl3-dyadic-building-action-soficity-forces-p-instability` for the current
  status of the action in `(P25)`.
