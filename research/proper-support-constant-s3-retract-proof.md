---
rg: 2
id: proper-support-constant-s3-retract-proof
kind: route
title: Compress every supported return to identity and keep the prime-field transvections
target: proper-support-returns-retain-constant-s3-retract
requires:
  - endpoint-j1-enlargement-has-native-s3-retract
---

Let `Q=rI`.  Equation `(PSR1)` says that `Q` commutes with every `W_i` and
that its corner restriction is the corner identity.  Since `n,m` have only
coefficients zero and one, they commute with `Q` as well.  Therefore

```text
pi:G -> GL_d(rRr),             g |-> QgQ               (1)
```

is a homomorphism.  It kills the `W_i` and maps `n,m` to

```text
n_r=rI+rE_ab,                 m_r=rI+rE_ba.            (2)
```

Because the characteristic is two and `r!=0`, the unital prime subring of
`rRr` is `{0,r}~=F_2`.  On the `(a,b)` block, `(2)` is the standard pair
of elementary matrices generating `GL_2(F_2)`.  It has six elements, so
`pi` is injective on the original constant copy `N=<n,m>`.  Composing `pi`
with the inverse `pi(N)->N` proves `(PSR3)`.

For the Leavitt application, `p+q=1` and `pq=qp=0`.  A depth-`k`
zero-prefix Whitehead has nonidentity coefficients among

```text
e_k=s_(0^k)t_(0^k),
e_(k+1),
c_k=s_(0^(k+1))t_(0^k),
d_k=s_(0^k)t_(0^(k+1)).                              (3)
```

Every coefficient in `(3)` is annihilated by `q` on both sides, because
its source and range cylinders lie under `p`.  Thus the Whitehead obeys
`(qI)W=W(qI)=qI`.  This applies independently to every member of the
family and proves `(PSR5)`.

Finally `s_00t_1` does not satisfy the same support condition:

```text
(s_00t_1)q=s_00t_1,             q(s_00t_1)=0.          (4)
```

So `B_2` does not commute with the scalar `qI` corner.  Equation `(4)`
proves only that the present scalar-corner lemma stops there.  It is not a
breaker statement: the sharper coordinate corner `q(E_77+E_88)` still
commutes with `B_2`, as proved in
`endpoint-native-heads-retain-coordinate-q-s3-retract`.
