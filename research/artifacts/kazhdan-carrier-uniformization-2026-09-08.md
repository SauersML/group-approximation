# Exact Kazhdan generators control arbitrary matrix carriers

2026-09-08. This closes the previously open matrix-form coprime
`SL_3(Z)<=SL_3(Z[1/p])` relative-embedding face. The input is the
established collapse of the exact coprime actor sector. The new bridge
uses coordinate commutants, so it never identifies a moving congruence
slot with an element of the constant-sequence lattice algebra.

## 1. The finite-matrix identity

Let `B subset M_d` be a unital star-subalgebra. Its commutant `B'` is
taken inside `M_d`. Averaging conjugations over the compact group
`U(B')` gives the normalized-trace-preserving conditional expectation:

    E_B(y)=integral_(U(B')) v y v* dv.                         (KC1)

Indeed the Haar average is the orthogonal projection on the fixed
subspace of the unitary conjugation action. That fixed space is `B''=B`
by the finite-dimensional bicommutant theorem. Expanding the square
and using that `E_B` is the Hilbert--Schmidt orthogonal projection gives

    integral_(U(B')) ||[v,y]||_2^2 dv
      =2||y||_2^2-2 Re tau(y* E_B(y))
      =2||y-E_B(y)||_2^2.                                  (KC2)

No irreducibility or multiplicity assumption is involved. In particular,
`B` may have many central blocks and arbitrary multiplicity spaces.

## 2. Uniform containment from a fixed Kazhdan set

Let `sigma:C->U(d)` be an exact representation of a group with
Kazhdan generating set `S` and constant `kappa`. Put `A=sigma(C)''`
and `R=A'`. Exactness makes `Ad sigma` a unitary representation on
`L^2(M_d)` with fixed subspace `R`. Thus

    ||v-E_R(v)||_2^2
      <=kappa^(-2)sum_(s in S)||[v,sigma(s)]||_2^2.          (KC3)

For `x in A`, the element `E_R(v)` commutes with `x`. Consequently

    ||[v,x]||_2^2
      <=4||x||_op^2||v-E_R(v)||_2^2.                       (KC4)

Integrate `(KC4)` and `(KC3)` over `U(B')`. Applying `(KC2)` to the
left side and separately to every source term proves

    dist_2(x,B)^2
      <=(4/kappa^2)||x||_op^2
          sum_(s in S)dist_2(sigma(s),B)^2.                (KC5)

The integration of the source terms is useful: replacing each source
commutator by twice its distance before integrating loses a factor of
two. The displayed coefficient follows directly by cancelling the two
Haar factors in `(KC2)`.

In particular, if `dist_2(sigma_k(s),B_k)->0` for the finitely many
`s in S`, then

    sup_(x in sigma_k(C)'', ||x||_op<=1)dist_2(x,B_k)->0.   (KC6)

This is a uniform statement about the coordinate image algebra. It does
not say that its ultraproduct equals `pi(C)''`. The latter equality is
false in the regular congruence examples already in the repository.

## 3. Auditing the coprime arithmetic input

Fix a prime `p`, put `Lambda=SL_3(Z)`, `Gamma=SL_3(Z[1/p])`, and
`h=diag(p,1,p^-1)`. Suppose `pi:Gamma->U(Q)` has coordinate-exact
restriction `sigma_k` to `Lambda`, factoring through
`SL_3(Z/n_k)` with `gcd(n_k,p)=1`. Let

    R_k=sigma_k(Lambda)',
    H_0=[sigma_k(h mod n_k)],
    H=pi(h).

The overlap `Lambda_-=Lambda cap h^-1 Lambda h` contains the principal
congruence subgroup `Lambda(p^2)`. To check this, write an element as
`I+p^2 X`; conjugation by `h` scales each entry by a power `p^j` with
`-2<=j<=2`, so every resulting entry remains integral. This corrects
the older proof's literal `Lambda(4)` when `p` is not two.

The overlap is finite index and hence has property (T). It surjects
onto `SL_3(Z/n_k)`: surjectivity of reduction modulo `p^2 n_k` and
the Chinese remainder theorem let an arbitrary residue modulo `n_k`
be represented by an integral matrix congruent to the identity modulo
`p^2`. Therefore the coordinate overlap and full-lattice commutants
both equal `R_k`. Kazhdan projection for these two fixed groups gives

    pi(Lambda)' cap Q
      =pi(Lambda_-)' cap Q=prod_omega R_k.                (KC7)

Both `H` and `H_0` implement conjugation by `h` on `Lambda_-`, so
`W=H_0*H` belongs to `prod_omega R_k`. It commutes with every constant
lattice matrix and with every moving congruence slot.

Let `w_12,w_23` be signed permutation matrices in `Lambda`. Set
`h'=w_12 h w_12^-1` and `h''=w_23 h w_23^-1`. Directly,

    h'=diag(1,p,p^-1),
    h''=diag(p,p^-1,1),
    h (h'')^-1=h'.                                      (KC8)

Conjugation fixes `W`, so the three represented diagonals are their
congruence slots times the same `W`. In `(KC8)`, the two copies of
`W` on the left cancel, whereas one remains on the right. The slots
already satisfy `(KC8)`, hence `W=1`. Thus `H=H_0`. For chosen unitary
representatives this means

    ||pi_k(h)-sigma_k(h mod n_k)||_2 -> 0                 (KC9)

along the given ultrafilter. This argument uses the coprime exact
sector, with no restriction on multiplicities or canonical trace.
It proves no statement about general approximate lattice tuples or
about arbitrary `p`-primary levels.

## 4. Closing the relative matrix witness face

Suppose in addition that unital subalgebras `B_k subset M_(d_k)`
form a scalar relative matrix witness:

    dist_2(pi_k(c),B_k)->0                 (c in Lambda),
    ||E_(B_k)(pi_k(g))||_2->0             (g outside Lambda).

The exact representatives `sigma_k(c)` agree with `pi_k(c)` in the
ultraproduct, so their generator distances also tend to zero. Apply
`(KC5)` to the moving unitary slot `sigma_k(h mod n_k)` and use `(KC9)`:

    dist_2(pi_k(h),B_k)
      <=||pi_k(h)-sigma_k(h mod n_k)||_2
        +(2/kappa)sqrt(sum_(s in S)dist_2(sigma_k(s),B_k)^2)
      ->0.                                               (KC10)

It follows that `||E_(B_k)(pi_k(h))||_2->1`, contradicting the
outside-element condition for `h`. This proves
`sl3-re-lambda-exact-coprime-face-is-unfaithful` with no logarithmic
rate condition. The exact arithmetic theorem and `(KC5)` supply an
honest new proof route; the old route using constant-sequence algebra
membership stays invalidated.

There is also a short qualitative proof that only uses the collapse
conclusion `(KC7)` plus `H=H_0`. By `(KC2)`, the outside expectation
condition allows a choice `v_k in U(B_k')` with

    ||[v_k,pi_k(h)]||_2^2
      >=2(1-||E_(B_k)(pi_k(h))||_2^2) ->2.

For each fixed `c in Lambda`,

    ||[v_k,pi_k(c)]||_2
      <=2 dist_2(pi_k(c),B_k)->0.

Thus `[v_k]` is a lattice-central unitary moved by `pi(h)` in the
same actor embedding, directly contradicting sector collapse.
The continuous integrand attains its maximum on the finite-dimensional
compact unitary group, so a choice at least as large as its average
exists at each coordinate.

## 5. Scope and source audit

The certificate here is an exact finite-matrix proof. No finite search,
numerical probe, or executable exhaustion is used. The Haar identity
was already used in the repository for `full-raw-packet-commutant-witness`;
the new step combines it with a Kazhdan gap to control all moving
coordinate algebra elements and close the arithmetic carrier leaf.

An independently supplied argument in
`kazhdan-jones-uniform-carrier-containment-2026-09-08.md` uses the Jones
basic construction to control all group unitaries in arbitrary finite
tracial coordinates by the maximum generator defect. That theorem is
stronger in ambient-algebra generality and has a sharper group-element
bound. The Haar theorem here instead controls the whole operator-norm
unit ball of the generated matrix algebra by the sum of squared
generator defects. These are distinct reusable statements; both give
valid proofs of the same coprime relative-matrix exclusion.

The scalar relative-embedding definition is
[Gao, Definition 2.2](https://arxiv.org/html/2012.07940v3#S2).
Its general format allows QWEP ambient coordinates and hyperfinite
carriers. The leaf closed here explicitly quantifies over matrix
coordinates; no coprime notion for arbitrary QWEP coordinates is
introduced. The distinction between strict and flexible stability is
as in [Dogon, Definition 1.2 and the discussion after Theorem
1.3](https://arxiv.org/html/2211.10492v3#S1). Infinite hyperlinear
Kazhdan groups fail strict HS stability; that fact does not refute
flexible stability and is not used in this argument.

On 2026-09-08 repository searches covered near containment, Haar
commutants, uniform algebra distance, and the existing coprime exact
claims and notes. Bounded external searches for Kazhdan near containment
and matrix subalgebra perturbation found related operator-norm
perturbation theory, but no source needed beyond the displayed elementary
argument. This is a new application within Cairn, not a priority claim
for the general inequality. No algorithmic novelty is asserted.

The full arithmetic non-relative-embedding statement remains open:
uncontrolled approximate lattice tuples and the unresolved primary
sectors are not eliminated by this proof. The proof does not construct
a nonhyperlinear group.
