# An unnormalized Schatten-one radical corner is already hyperlinear

Date: 2026-08-13

## 1. Result

Let

```text
Rad_sof(E)=intersection_(phi:E->S, S sofic) ker(phi).
```

Use the **unnormalized** Schatten-one norm

```text
||A||_1=Tr(|A|).
```

**Theorem.**  Let `E` be countable and let `z in E` satisfy

```text
z != 1,       z^2=1,       z central in E,
z in Rad_sof(E).                                           (S1R1)
```

Suppose there are maps `phi_n:E->U(d_n)` which are asymptotically
multiplicative in unnormalized Schatten one norm and retain `z`.  More
explicitly,

```text
||phi_n(gh)-phi_n(g)phi_n(h)||_1 -> 0                 (S1R2)
```

for every fixed `g,h`, while

```text
liminf_n ||phi_n(z)-1||_1 > 0.                         (S1R3)
```

Then a hyperlinear nonsofic group exists.  In particular, if `E` is
Schatten-one approximated in the sense of Bachner--Dogon--Lubotzky, then its
central radical involution `(S1R1)` produces a hyperlinear nonsofic image.

This is an unnormalized-`L1` analogue of the operator-norm finite-radical
corner theorem.  It needs neither hyperlinearity of `E/<z>` nor a
positive-density negative `z`-spectral sector in the original matrices.

## 2. Exactification of the involution

First `(S1R2)` at `(1,1)` makes `phi_n(1)` tend to the identity in
Schatten one norm, because multiplication on the left by the unitary
`phi_n(1)` identifies the two errors.  Apply the involution-rounding lemma
to `phi_n(z)`.  The relation `z^2=1` and `(S1R2)` then give exact
self-adjoint unitaries `u_n` such that

```text
u_n^2=1,       ||u_n-phi_n(z)||_1 -> 0.                (S1R4)
```

Put

```text
q_n=(1-u_n)/2.                                         (S1R5)
```

Thus `q_n` is the negative spectral projection of `u_n`.  Condition
`(S1R3)` makes `q_n` nonzero for all large `n`: if `q_n=0`, then `u_n=1`,
contradicting `(S1R3)` and `(S1R4)`.  Centrality of `z`, together with
`(S1R2)`, gives

```text
||[phi_n(g),q_n]||_1 -> 0,       g in E.               (S1R6)
```

Indeed `phi_n(g)` asymptotically commutes in Schatten one norm with
`phi_n(z)`, hence with `u_n` and its affine spectral projection `q_n`.

The compression and polar-correction lemma for unitarily invariant norms
therefore gives maps

```text
psi_n:E->U(q_n C^(d_n))                                (S1R7)
```

which are asymptotically multiplicative in unnormalized Schatten one norm.
Writing `r_n=rank(q_n)>=1`, every resulting multiplication error `A_n`
satisfies `||A_n||_op<=2` and hence

```text
||A_n||_(2,r_n)^2
 =Tr(A_n^*A_n)/r_n
 <=2 Tr(|A_n|)/r_n
 <=2||A_n||_1 ->0.                                    (S1R8)
```

Thus `(psi_n)` is a normalized Hilbert--Schmidt asymptotic representation
on the nontrivial corner, regardless of how small `r_n/d_n` is.

## 3. The radical involution survives the renormalized corner

On the negative corner, the rounded involution is exactly minus the
identity:

```text
q_n u_n q_n=-q_n.                                      (S1R9)
```

The compression and polar-correction estimates from `(S1R7)`, together
with `(S1R4)`, therefore give

```text
||psi_n(z)+1||_1 -> 0.                                 (S1R10)
```

Since the operator norm of the difference is at most two,

```text
||psi_n(z)+1||_(2,r_n)^2
 <=2||psi_n(z)+1||_1/r_n
 <=2||psi_n(z)+1||_1 ->0.                             (S1R11)
```

Consequently `||psi_n(z)-1||_(2,r_n)->2`: the radical involution becomes
the scalar `-1` in the tracial ultraproduct.

If desired, tensor every corner with an identity matrix so that its
dimension tends to infinity; neither `(S1R8)` nor the conclusion following
`(S1R11)` changes.
Choose a free ultrafilter and let `L` be the image of `E` in the resulting
tracial matrix ultraproduct.  Equation `(S1R8)` makes `L` hyperlinear, while
`(S1R11)` says that the quotient map `E->L` retains `z`.

If `L` were sofic, this quotient map would have to kill every element of
`Rad_sof(E)`, contradicting `(S1R1)` and `(S1R11)`.  Hence `L` is
hyperlinear and nonsofic.

## 4. Scaling boundary

The argument works because the original norm is **unnormalized**.  A
nonzero corner has rank at least one, so `(S1R8)` turns absolute trace-norm
error into normalized Hilbert--Schmidt error with no density loss.

There is no analogous implication from a normalized Schatten-one or
normalized Hilbert--Schmidt model: dividing by the original ambient
dimension permits the entire error to concentrate on the selected
`o(d_n)` corner.  Conversely, Bachner--Dogon--Lubotzky's inapproximability
theorem does not prove nonhyperlinearity, because a normalized
Hilbert--Schmidt microstate need not have unnormalized Schatten-one defect
tending to zero.

For the explicit cyclic-shear group already constructed in this repository,
the central involution belongs to the full sofic radical.  The theorem
therefore reduces a new sufficient endpoint to one line:

```text
cyclic shear is unnormalized-Schatten-one approximated
    ==> a hyperlinear nonsofic group exists.                        (S1R12)
```

No such approximation is asserted here.  The endpoint is weaker than the
operator-norm MF endpoint in its finite-corner conversion, but the two
approximation hypotheses are incomparable without a dimension-versus-error
rate.

## Reference

- B. Bachner, A. Dogon, and A. Lubotzky, *On L1-approximation of groups*,
  arXiv:2508.17392v3, especially Lemmas 2.2--2.3 and Proposition 2.4.
