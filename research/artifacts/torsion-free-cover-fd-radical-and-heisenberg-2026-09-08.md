# The cover's exact finite-dimensional radical, and why computing it is not a transfer

2026-09-08.  Second ingestion into the torsion-free transfer region opened by
`research/artifacts/torsion-free-transfer-covers-and-obstructions-2026-09-08.md`.

An external audit was asked to settle the torsion-free non-MF transfer.  It
stated, correctly and up front, that it had **not** settled it, and that it
supplies no justification for deleting the archive's existing torsion-free
construction.  What it supplies instead is one exact computation about the
canonical cover and one explicit counterexample to the inference that would
otherwise appear to finish the job.  Both are re-derived below; both are
landed as claims.

The whole point is the difference between two radicals that the archive
already distinguishes:

```text
Rad_MF(K) = intersection of kernels of homomorphisms K -> U(Q),
            Q = prod_n M_(d_n) / sum_n M_(d_n),
Rad_fd(K) = intersection of kernels of exact finite-dimensional
            unitary representations K -> U(d).
```

A finite-dimensional unitary representation is a constant-sequence corona
representation, so `Rad_MF <= Rad_fd` always
(`five-radicals-from-residually-finite-target` records the chain
`Rad_MF <= Rad_fd <= Res_fin`, formalized as `linearResidual_le_fdUnitaryResidual`
in `GroupApproximation/Sofic/LinearResidual.lean`).  The inclusion runs the
wrong way for a transfer: `K` is non-MF exactly when `Rad_MF(K) != 1`, and
knowing `Rad_fd(K) != 1` -- even knowing `Rad_fd(K)` exactly -- constrains the
larger group.

## 1. The cover, with a dummy generator

Fix a countable `G`, a countable generating set `X`, and add one generator `z`
that maps to the identity:

```text
F = F(X u {z}),   q : F ->> G,   q(z) = 1,   R = ker q,
E = F/[R,R],      A = R/[R,R].
```

Torsion-freeness of `E` and freeness of the abelian kernel `A` are
`free-abelianized-cover-is-torsion-free`, already established here; the dummy
generator changes nothing about that (it enlarges `F` by one free generator
and `R` by the normal closure of `z`).  What the dummy generator buys is a
**presentation-independent detector**.

Define `D : F -> Z[G]` by

```text
D(x) = 0  (x in X),   D(z) = 1,   D(uv) = D(u) + q(u) D(v),
```

with `D(s^-1) = -q(s)^-1 D(s)` on generators; deleting an adjacent inverse pair
leaves the value unchanged, so `D` is well defined on reduced words.  This is
the Fox derivative `d/dz` pushed to `Z[G]`.  On `R` it is a homomorphism into
an abelian group (because `q(r) = 1` there), so it kills `[R,R]`, and for
`q(f) = g`,

```text
D(f z f^-1 z^-1) = g - 1.                                            (DET)
```

Hence, writing bars for images in `E`,

```text
g != 1   ==>   [fbar, zbar] != 1  in E.                              (NT)
```

No hypothesis on the presentation of `G` is used, which is exactly why the
dummy generator is there.

## 2. What an exact finite-dimensional representation of the cover can see

Let `rho : E -> U(d)`.  The commuting unitaries `rho(A)` decompose `C^d` into
joint eigenspaces

```text
C^d = H_1 (+) ... (+) H_k,   rho(a)|_(H_j) = chi_j(a) I,             (EIG)
```

with the `chi_j` distinct.  (Split off eigenspaces of one non-scalar unitary
of the family and recurse; each split drops a dimension, so the process stops,
and no finite generation of `A` is needed.)  Normality of `A` makes `E`
permute the `H_j`; `A` fixes each of them, so the permutation homomorphism
factors through `G`:

```text
G -> Sym(k).                                                         (PERM)
```

**(2a) Non-residual-finiteness already gives a nontrivial `Rad_fd`.**  Let
`g != 1` lie in the finite residual `Res_fin(G)` and take `q(f) = g`.  Then
`(PERM)` kills `g`, so `rho(fbar)` preserves every `H_j`, on which `rho(zbar)`
is a scalar (`z` lies in `R`).  So `rho([fbar,zbar]) = I` for **every** `rho`,
while `(NT)` says the element is nontrivial:

```text
G not residually finite   ==>   Rad_fd(E) != 1.
```

Non-MF implies non-residually-finite (residually finite groups are MF), so
this holds for every non-MF input.

**(2b) Full MF radical downstairs collapses the cover's finite-dimensional
theory entirely.**  Suppose `Rad_MF(G) = G`, i.e. every homomorphism from `G`
to a countable MF group is trivial (`universal-mf-quotient`; the archive calls
this a *full MF radical*).  Finite groups are MF, so `(PERM)` is trivial and
every `H_j` is `E`-invariant.  On `M_(dim H_j)(C)` with the Hilbert-Schmidt
inner product, `B -> rho(e)|_(H_j) B rho(e)|_(H_j)^*` is a finite-dimensional
unitary representation of `E` that kills `A` (scalars), hence factors through
`G`, and whose image is a countable subgroup of a unitary group, hence MF.
The hypothesis makes it trivial, so `rho(e)|_(H_j)` commutes with every matrix
and is scalar.  Therefore every `rho` has abelian image and

```text
[E,E] <= Rad_fd(E).
```

Conversely `[R,R] <= [F,F]`, so `E/[E,E] = F/[F,F]` is free abelian on
`X u {z}`, and characters separate a free abelian group of any rank (send a
coordinate with nonzero entry `m` to a primitive `p`-th root of unity for a
prime `p` not dividing `m`).  So

```text
Rad_MF(G) = G   ==>   Rad_fd(E) = [E,E],   nontrivial by (NT).
```

This is an exact theorem about `E`, with no approximation anywhere in it.

## 3. Why (2b) is not the transfer

The tempting reading of (2b) is: the cover has no finite-dimensional theory
beyond its abelianization, therefore the cover is not MF, therefore
`torsion-free-countable-non-mf` is closed with no Property (T) input.  The
middle step is false, and the following group shows it in exactly the shape
(2b) produces.

Let `H = UT_3(Q)`, written on `Q^3` by

```text
(a,b,c)(a',b',c') = (a+a', b+b', c+c'+ab').                          (H1)
```

Then `(a,b,c)^n = (na, nb, nc + C(n,2) ab)`, so `H` is torsion-free.  With
`x(a) = (a,0,0)`, `y(b) = (0,b,0)`, `z(c) = (0,0,c)`,

```text
[x(a), y(b)] = z(ab),                                                (H2)
```

so `[H,H] = Z = z(Q)`, the centre, and `H/Z = Q^2`.

**Every exact finite-dimensional unitary representation of `H` kills `Z`.**
`Z` is central, so its joint eigenspaces are `H`-invariant; on a block of
dimension `m` write the central character as `chi : Q -> U(1)`.  A matrix
commutator has determinant `1`, so `(H2)` gives `chi(ab)^m = 1` for all
`a,b in Q`.  Take `a = c/m` and `b = 1`:

```text
chi(c) = chi(c/m)^m = 1.
```

Characters of `Q^2` separate points, so

```text
Rad_fd(H) = [H,H] = Z != 1.                                          (H3)
```

**And `H` is MF.**  Every finitely generated subgroup of `H` has coordinates
in some `Z[1/N]`, and `UT_3(Z[1/N])` is residually finite (reduce modulo a
prime `p` not dividing `N` nor the numerator of a nonzero coordinate).  So `H`
is locally residually finite, hence LEF, hence operator MF by
`lef-implies-operator-mf` -- which is the archive's own certified route, and
avoids the amenable-implies-MF step that `permutation-norm-models-certify-exactly-lef`
records as uncertified here.  The audit's explicit models are the concrete LEF
windows: choose increasing primes `p_n`, put `V_n(h) = lambda_n(hbar)` using
the left regular permutation representation of `UT_3(F_(p_n))` whenever the
coordinates of `h` reduce, and `V_n(h) = I` otherwise.  For each fixed pair
`h,k` all denominators are invertible for large `n`, so `V_n(hk) = V_n(h)V_n(k)`
eventually; and for `h != 1`, `hbar != 1` for large `n`, so

```text
||V_n(h) - I|| >= ||(V_n(h)-I) e_1|| = ||e_(hbar) - e_1|| = sqrt 2.
```

The induced map into the norm-matrix corona is therefore an injective
homomorphism.

So `H` is torsion-free, MF, and satisfies precisely the conclusion of (2b):
its exact finite-dimensional theory is nothing but its abelianization.  The
inference "`Rad_fd(K) = [K,K] != 1` therefore `K` is not MF" is refuted, and
refuted inside the torsion-free class.

**Where the refutation bites.**  The determinant argument uses `c/m`, an
element that changes with the representation dimension `m`.  Pointwise
asymptotic multiplicativity gives no control on a moving element, so no MF
model is obliged to reproduce it.  This is the same wall as
`fd-mark-stability-forces-mf-invisibility`: passing from `Rad_fd` to `Rad_MF`
needs a stability hypothesis at the mark, and nothing in (2b) supplies one.

## 4. What is and is not closed

- `free-abelianized-cover-reflects-mf` -- the isolated implication
  `F/[R,R] MF => F/R MF` -- is **untouched**.  `H` is not a counterexample to
  it and is not claimed to arise from a full-MF-radical input.
- No impossibility theorem for transfers in general is proved.  Section 3
  kills one inference, not a class of procedures; the class-level no-go on
  central kernels is the separate
  `torsion-free-central-cover-forces-abelian-finite-subgroups`.
- The existing torsion-free non-MF construction stands.  Nothing here
  justifies removing it.

## Relation to what the archive already had

Two neighbouring calibrations were already established here, and neither
subsumes section 3:

- `bare-self-copy-mf-calibration` gives a torsion-free finitely presented
  operator-MF group with **one** finite-dimensionally invisible mark.  Its
  `Rad_fd` is not the whole commutator subgroup -- `BS(1,2)` is residually
  finite and supplies representations with nonabelian image -- so it does not
  match the shape (2b) delivers.
- `abels-prufer-quotient-is-fp-sofic-with-fd-invisible-center` gives a
  finitely presented sofic group with a central mark of order `p` invisible to
  every exact finite-dimensional representation.  Its mark is torsion and its
  conclusion is sofic (Hilbert-Schmidt), not MF (operator norm).

The rational Heisenberg group is the witness that is simultaneously
torsion-free, operator MF, and totally collapsed
(`Rad_fd = [H,H]`, every finite-dimensional representation abelian).  That
combination is what a counterexample to the (2b) inference has to be.

## Provenance

The external note worked offline, reported reading a handful of framework and
relation-module records for orientation, used no archive theorem as a
mathematical ingredient, and performed no proof-assistant verification.  All
four of its arguments (the crossed-word detector, the eigenspace factorization,
the determinant identity, the finite matrix models) were re-derived here before
landing.  Two of its steps were replaced by archive citations rather than
re-authored: MF of a countable subgroup of `U(m)` by constant sequences
(`five-radicals-from-residually-finite-target`), and MF of the rational
Heisenberg group by `lef-implies-operator-mf` instead of a from-scratch corona
argument.  Torsion-freeness of the cover is the already-landed
`free-abelianized-cover-is-torsion-free` and is cited, not restated.

No Lean was written or built for this region, and nothing here is
machine-checked.
