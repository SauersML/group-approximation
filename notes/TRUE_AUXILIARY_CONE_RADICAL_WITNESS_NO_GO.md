# Bounded auxiliary cones cannot retain a sofic-radical witness

Date: 2026-08-11

## Outcome

The open-path escape left in
`TRUE_A3_METRIC_CONE_SYNCHRONIZATION.md` closes for the witness which occurs
in the hyperlinear-versus-sofic problem.

Let

```text
P=<S | R>,       w in Rad_sof(P),
```

and let `C_rad<infinity` be the linear finite-action constant

```text
d_rho(w)<=C_rad sum_(r in R)d_rho(r).                 (ACR1)
```

Suppose a finite auxiliary connection encodes the `w`-path over every point
of a finite `F(S)`-set.  On points moved by `w`, its contribution is bounded
by the moved fraction, which is controlled by `(ACR1)`.  On points fixed by
`w`, the encoded path is closed, so a bounded metric cone controls its
holonomy by curvature.  Quantitatively, if the encoded paths have bounded
length and bounded weighted edge congestion, then

```text
average w-holonomy energy
 <= cone_constant * curvature_energy
    + diameter_constant * C_rad * relator_motion.     (ACR2)
```

Thus vanishing curvature and vanishing relator motion force the marked
holonomy to vanish.  Repeating the word over a balanced orbit of open paths
does not evade the obstruction: radical membership makes those paths closed
on `1-o(1)` of the base.

For the `A_3(F_q)` nine-triangle synchronization theorem, a path orbit of
length at most `L` has the explicit RMS estimate

```text
E_x ||Hol_phi(gamma_x)-1||_2^2
 <=243 L^2 ||K_phi||_(2,T)^2
    +4 C_rad sum_(r in R)d_rho(r).                    (ACR3)
```

The constant is independent of `q` and of the matrix dimension.  Therefore
an orbit-redundant bounded-length `A_3` encoding cannot be the missing TRUE
bridge.  To retain a radical witness, an auxiliary construction must pay
unbounded path congestion/length, fail to make its base relators accurate,
or leave curvature bounded away from zero.  None is a dimension-free
synchronization theorem.

## 1. Abstract repaired-connection estimate

Let `F=F(S)` act on a nonempty finite set `Omega` through `rho`.  Let `Y` be
a finite graph, let `Lambda` be a group with a conjugation-invariant
subadditive length `ell`, and assume

```text
ell(g)<=D for every g in Lambda.                       (ACR4)
```

Let `phi` and `theta` be two `Lambda`-connections on `Y`.  For every
`x in Omega`, choose an oriented path `gamma_x` of length at most `L`.
Assume

```text
rho(w)x=x  ==>  gamma_x is closed.                    (ACR5)
```

The paths may otherwise have arbitrary endpoints.  Put

```text
epsilon_e=ell(phi(e)^(-1)theta(e)),

C_E=max_e ((1/|Omega|) sum_x N_e(gamma_x))/c_Y(e),    (ACR6)
```

where `c_Y` is a probability weight on the unoriented edges.

**Theorem 1 (radical open-path estimate).**  If `theta` has trivial
holonomy on every closed path and `(ACR1)` holds, then for every
`1<=r<infinity`,

```text
(1/|Omega|) sum_(x:rho(w)x=x) ell(Hol_phi(gamma_x))^r
 <=L^(r-1) C_E sum_e c_Y(e) epsilon_e^r,              (ACR7)
```

and, after charging every moved point by the diameter bound,

```text
(1/|Omega|) sum_x E_w(x)
 <=L^(r-1) C_E sum_e c_Y(e) epsilon_e^r
    +D^r C_rad sum_(a in R)d_rho(a).                  (ACR8)
```

Here `E_w(x)=ell(Hol_phi(gamma_x))^r` on fixed points, while on
moved points `E_w(x)` may be any nonnegative witness contribution bounded
by `D^r`.

**Proof.**  If `rho(w)x=x`, equation `(ACR5)` makes `gamma_x` closed and
the hypothesis on `theta` gives `Hol_theta(gamma_x)=1`.  Telescoping the two
path products and using conjugation invariance gives

```text
ell(Hol_phi(gamma_x))
 <=sum_(e in gamma_x) epsilon_e.                      (ACR9)
```

Convexity gives

```text
ell(Hol_phi(gamma_x))^r
 <=L^(r-1) sum_(e in gamma_x)epsilon_e^r.             (ACR10)
```

Sum `(ACR10)` over the fixed points.  Enlarging the nonnegative sum to all
`x`, interchanging the sums, and applying `(ACR6)` proves `(ACR7)`.

The moved points contribute at most `D^r d_rho(w)`.  Apply `(ACR1)` to this
term and add `(ACR7)`, proving `(ACR8)`.  End proof.

The statement deliberately uses the finite-action defect before passing to
an ultraproduct.  No assertion that `rho` factors through `P` is needed.

## 2. A repair operator supplies `theta`

Suppose an auxiliary two-complex has a metric synchronization theorem

```text
||a dot phi||_(r,E)<=K ||K_phi||_(r,T).               (ACR11)
```

Set

```text
theta_a(u,v)=a(u)^(-1)a(v).                           (ACR12)
```

This connection has trivial holonomy on every closed path, and

```text
epsilon_e=ell(phi(e)^(-1)theta_a(e))
          =ell((a dot phi)(e)).                       (ACR13)
```

Substituting `(ACR11)` into `(ACR8)` gives

```text
average witness energy
 <=L^(r-1) C_E K^r ||K_phi||_(r,T)^r
    +D^r C_rad Def_R(rho).                            (ACR14)
```

This is the promised general form of `(ACR2)`.

## 3. The `A_3(F_q)` constant

For `Y=A_3(F_q)`, the metric cone theorem gives `K=9`.  If the paths are the
uniform `GL_4(F_q)` orbit of one path of length at most `L`, then

```text
C_E<=3L.                                              (ACR15)
```

Take normalized Hilbert--Schmidt length and `r=2`.  Its diameter is `D=2`.
Equations `(ACR14)--(ACR15)` give

```text
average witness energy
 <=3 * 9^2 L^2 ||K_phi||_(2,T)^2
    +2^2 C_rad Def_R(rho),                            (ACR16)
```

which is exactly `(ACR3)`.

For normalized Hamming length, `D=1`, and the same argument gives

```text
average witness energy
 <=243 L^2 ||K_phi||_(2,T)^2
    +C_rad Def_R(rho).                                (ACR17)
```

The identical conclusion holds for any fixed `r`; only the displayed
constant changes.

## 4. Consequence for the universal character-transfer program

The relevant marked word is not an arbitrary word.  Finite-presentation
localization places it in `Rad_sof(P)`, and
`TRUE_LINEAR_SOFIC_RADICAL_INEQUALITY.md` supplies `(ACR1)`.  Therefore the
two apparent witness-preservation options in a bounded auxiliary cone are
both closed:

1. if the endpoint moves, its mass is at most `C_rad Def_R(rho)`;
2. if the endpoint does not move, the path is closed and `(ACR7)` controls
   its holonomy.

Consequently the open-path estimate in the `A_3` note is a useful general
metric theorem, but it cannot turn a unitary radical witness into a finite
permutation witness by any bounded-length, bounded-congestion encoding.  A
proposal with positive-density endpoint motion would already violate the
defining finite-action inequality for the sofic radical; it would amount to
constructing the desired sofic separation before applying the cone.

The live TRUE targets therefore return to the genuinely unresolved gates:

* construct a common Cartan and control its fixed-point phases without a
  bounded auxiliary-cone encoding; or
* prove the domination-constant implication directly on normal
  finite-dimensional characters.

Future compute should not search bounded `A_3` path encodings.  If an
auxiliary-complex search is retained, it must explicitly report the growth
of `L^(r-1)C_E`; bounded values are ruled out by `(ACR14)`.
