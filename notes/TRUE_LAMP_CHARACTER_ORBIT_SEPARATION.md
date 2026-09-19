# Lamp separation by a Hilbert embeddable length is an orbit-counting number

Date: 2026-08-14

## 0. Setting

Let `K` be a finite group with an **abelian** normal subgroup `L` (the lamps)
and quotient `A = K/L` (the acting part).  In the situation of interest
`L = (Z/2)^Sites` for a finite `A`-set `Sites`, and `A` is a finite model of the
acting group.  By `hilbert-embeddable-is-representation-realized`, every
Hilbert embeddable invariant length on `K` with `ell(1)=0` is

```text
ell = sum_(chi in Irr(K), chi != triv) a_chi psi_chi,   a_chi >= 0,
psi_chi(h) = chi(1) - Re chi(h) = (1/2)||pi_chi(h) - 1||_F^2.       (LC1)
```

Split `Irr(K) ∖ {triv}` into

* `Irr_I` — those with `L ⊆ ker chi`, i.e. inflated from `A`;
* `Irr_II` — the rest.

Write `ell = ell_I + ell_II` accordingly.  Both summands are nonnegative and
conditionally negative definite, and the splitting is unique.

## 1. The acting part is invisible on the lamps

For `chi in Irr_I` and `h in L` we have `chi(h) = chi(1)`, so
`psi_chi(h) = 0`.  Hence

```text
ell_I|_L = 0.                                                        (LC2)
```

**All lamp separation is carried by `ell_II`.**  This is the exact form of the
obstruction noted by `cairn-survivor` — "characters pulled back from the acting
quotient are trivial on the lamps" — restated as a decomposition of the cone
rather than as a failure of a hypothesis.  Two immediate consequences:

* the character-gap corollary must be applied to the `Irr_II` subcone, and the
  hypothesis it needs is only a **relative** gap: a uniform `kappa > 0` with
  `psi_chi(h)/chi(1) >= kappa` for `chi in Irr_II` and `1 != h in L`;
* since `ell_I, ell_II >= 0`, every upper constraint `ell <= epsilon` is
  inherited by each summand separately, so `ell_I` may be discarded whenever the
  separation being asked for is at a lamp element.

## 2. Clifford theory computes the relative gap exactly

Let `chi in Irr_II`.  Since `L` is abelian and normal, Clifford's theorem gives

```text
chi|_L = e * (theta_1 + ... + theta_t),                              (LC3)
```

where `{theta_1, ..., theta_t}` is a single `K`-orbit of **linear** characters
of `L`, all nontrivial (a trivial constituent would force `L ⊆ ker chi`, i.e.
`chi in Irr_I`), and `chi(1) = e t`.  Therefore for `h in L`

```text
psi_chi(h)/chi(1) = 1 - (1/t) sum_(i=1)^t theta_i(h).                (LC4)
```

So the relative gap at `h` is governed entirely by the **fraction of the orbit
that is nontrivial at `h`**, and `e` cancels.

Specialize to `L = (Z/2)^Sites`.  Characters correspond to subsets
`S ⊆ Sites` via `theta_S(a) = (-1)^(|{s in S : a_s = 1}|)`, and the `K`-action
on characters is the `A`-action on subsets.  For a lamp element `a` with
support `supp(a)`,

```text
psi_chi(a)/chi(1) = 2 * |{S in orbit : |S ∩ supp(a)| is odd}| / t.   (LC5)
```

Two cases carry the whole discussion.

* **Single lamp** `a_p`: `psi_chi(a_p)/chi(1) = 2 * (fraction of the orbit
  containing p)`.
* **Two-site mark** `w = a_p a_q`: `psi_chi(w)/chi(1) = 2 * (fraction of the
  orbit containing exactly one of p, q)`.

Since a general `ell_II` is a nonnegative combination of the `psi_chi`, the
normalized separation `ell(w)/(sum_chi a_chi chi(1))` is a convex combination of
the numbers in `(LC5)`.

## 3. What this settles

**Dilution is not the obstruction.**  The recorded constraint "no dilution of a
single lamp" was the worry that a model could make individual lamps
asymptotically invisible.  By `(LC5)` the separation of the two-site mark is
exactly twice the orbit fraction separating the two marked sites, and a
*generic* orbit of subsets separates two distinct sites on a fraction tending to
`1/2`.  So as soon as the model keeps `p` and `q` **distinct as sites**, some
orbit — indeed almost every orbit — gives the mark a separation bounded below by
an absolute constant, with no dependence on the number of sites.  The
`1/|A|`-style dilution feared for the normalized support length is an artifact of
choosing the *wrong* cone generator, not a constraint of the problem.

**The obstruction is relocated, not removed.**  What `(LC5)` needs is that the
finite model keeps the two marked sites distinct.  That is precisely the demand
that the recorded "no finite-quotient witness" constraint denies for genuine
quotients: in a finite quotient the compression `t Gamma t^(-1) <= Gamma`
becomes an equality and the two marked cosets are identified, so `p = q`, every
orbit fraction in `(LC5)` is zero, and the mark has length zero in every
Hilbert embeddable length.  The character theory therefore reproduces
`finite-quotient-blindness` exactly, and the design problem is unchanged in
substance: keep two specified sites distinct while the site map is only
approximately multiplicative.

**The character-gap route does not close the argument.**  Granting even the full
relative gap of §1, it constrains `ell_II` only on `L`.  The two-site rigidity
theorem puts the entire defect on the acting part, i.e. **off** `L`, where the
relative gap says nothing.  So "a vanishing defect must vanish identically" is
available for lamp-supported defects only, and the rigidity theorem says there
are none.  The two results are consistent rather than contradictory, and their
combination yields no obstruction.  This is a negative result about the route,
and it should be recorded as one rather than left looking promising.

## 4. Scope

Proved here: `(LC2)`, `(LC4)`, `(LC5)`, and the three conclusions of §3.  Uses
`hilbert-embeddable-is-representation-realized` for the cone description and
Clifford's theorem for `(LC3)`; `L` abelian is used exactly once, to make the
constituents linear so that `e` cancels in `(LC4)`.

Not proved: that a finite model keeping the two marked sites distinct exists or
does not exist; anything about the acting part's contribution; any bound on the
defect.
