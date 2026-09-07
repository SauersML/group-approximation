# Kaplansky: exact finite-precision trace obstructions

## Scope and status, checked 2026-09-07

This is a complete proof of the finite-precision statements below, **not a
proof of Kaplansky's Direct Finiteness Conjecture**. No inverse pair or
unconditional direct-finiteness theorem for arbitrary groups is obtained.
The existing Leavitt target remains open. The argument gives a terminating
obstruction calculation for each specified precision, a sufficient precision
for finite-subgroup projectives, and examples proving that no fixed precision
works for all nonzero scalar idempotents.

The lifted-trace construction is established mathematics, not a new method:
Daniel R. Farkas and Zbigniew S. Marciniak, *Lifting idempotents in group
rings*, J. Pure Appl. Algebra 25(1) (1982), 25--32,
https://doi.org/10.1016/0022-4049(82)90093-7; see also
Farrell--Linnell, *Whitehead groups and the Bass conjecture*, Section 5,
https://arxiv.org/abs/math/0301205. The repository already gives the p-adic
construction and finite-subgroup rank formula in
`lifted-trace-finite-subgroup-proof`. The contribution here is its explicit
finite certificate interface, precision bound, and scalar sharpness family.
No literature-priority claim is made for these elementary consequences.

For the problem-status check, the primary paper Elek--Szabo,
https://arxiv.org/abs/math/0305440, proves the sofic case. The August 2026
Leavitt-unit-group preprint https://zenodo.org/records/21840947 reports bounded
searches and explicitly reports no counterexample. The older problem page
https://blog.spp2026.de/blog/kaplanskys-direct-finiteness-conjecture/ is dated
2021; its assertion about the then-absence of nonsofic examples is not used
as a current-status claim. These sources provide no general resolution.

## 1. A finite polynomial lift

Fix a prime p, an integer k >= 1, a group G, and an idempotent
e in M_n(F_p[G]). Work in B_k = (Z/p^k Z)[G]. Choose any coefficient lift
a_0 in M_n(B_k) of e and set

    a_(j+1) = 3 a_j^2 - 2 a_j^3.

With delta_j = a_j^2-a_j, polynomial expansion gives

    a_(j+1)-a_j = (1-2a_j) delta_j,
    delta_(j+1) = delta_j^2 (4 delta_j-3).

These identities hold in a noncommutative ring: every factor is a polynomial
in the single element a_j. Inductively delta_j belongs to p^(2^j) M_n(B_k).
All a_j reduce to e modulo p. Thus after any r with 2^r >= k,

    E = a_r,       E^2=E,       E mod p=e.                 (1)

At k=1 no iteration is needed. Each iterate has finite support. This is a
finite algebraic construction, with at most ceil(log_2 k) rounds; it asserts
no bound on the cost of group multiplication or on the growth of support.
An algorithmic implementation requires exact equality and multiplication
for its group elements. An arbitrary presentation does not provide those.

## 2. Lifted trace modulo p^k is an invariant

For a square matrix A over B_k let T(A) be the sum of the coefficients of
the group identity in its diagonal entries. For rectangular compatible X,Y,

    T(XY) = sum_(i,j,g) X_ij(g) Y_ji(g^-1) = T(YX).       (2)

The sums are finite and coefficients commute. Suppose E,E' are two
idempotent lifts of the same e. Then

    W = E'E + (1-E')(1-E)

is 1 modulo p and satisfies WE=E'W. Every matrix 1+z with z in pM_n(B_k)
is invertible by the finite geometric series, because z^k=0. Hence E and
E' are conjugate and have the same T.

Next suppose e and f represent isomorphic projectives (possibly in
different matrix sizes). Choose corner matrices x,y with

    xy=e,       yx=f,       x=exf,       y=fye.

For chosen lifts E,F, lift x,y to X=EX_0F and Y=FY_0E. In the E-corner,
XY reduces to its identity E. Thus XY has a corner inverse U. Set Y'=YU;
then XY'=E. The matrix P=Y'X is idempotent, lies in the F-corner, and reduces
to f. Therefore D=F-P is an idempotent in pM(B_k). But that ideal is
nilpotent, so D=D^k=0. Consequently Y'X=F and (2) gives T(E)=T(F).

The well-defined invariant

    t_(p,k)([e]) = T(E) in Z/p^k Z                       (3)

is additive under block sum. It therefore defines a homomorphism on
K_0(F_p[G]). In particular it is unchanged by an isomorphism after adding
the same arbitrary finitely generated projective to both sides. Reducing
an idempotent lift from precision k+1 to k proves compatibility of the
invariants, and their inverse limit is the repository's t_p in Z_p.

If AB=I_n over F_p[G], P=BA is idempotent and equivalent to I_n via A,B.
Its complement d=I_n-BA is idempotent, and P+d=I_n is an orthogonal sum.
Therefore

    t_(p,k)([d]) = 0 for every k >= 1.                   (4)

Likewise equivalent e,f must have equal values in (3). A nonzero residue
is an exact obstruction, allowing arbitrary ambient supports for potential
intertwiners. A zero residue is **inconclusive**. Even vanishing for all k
is only a necessary condition here; faithfulness on arbitrary projectives
has not been proved.

## 3. A sufficient precision for finite-subgroup idempotents

Let H <= G be finite, |H|=m=p^h m' with p not dividing m', and let
0 != e in M_n(F_p[H]), n >= 1. Define

    d = dim_(F_p) image(e : F_p[H]^n -> F_p[H]^n).

The finite-subgroup rank formula is

    t_p([e F_p[G]^n]) = d/m.                            (5)

For completeness, carry out the same polynomial iteration in
M_n(Z_p[H]). Its limit E is idempotent: the defect valuations double and
successive differences tend to zero. The image of E on the finite free
Z_p-module Z_p[H]^n is a direct summand, hence free; reduction modulo p
shows its rank is d. The ordinary trace of this idempotent over Q_p is d.
Left multiplication by a nonidentity element of H has zero regular trace,
whereas the identity has regular trace m. Hence m T(E)=d. Computing T
after embedding H in G does not change its value. This proves (5).

Since T(E) is p-adically integral, p^h divides d. Put a=d/p^h. Then

    1 <= a <= n m',       t_p([e])=a/m'.

For every k such that

    p^k > n m',                                         (6)

the integer a is nonzero modulo p^k, and m' is invertible modulo p^k.
Thus t_(p,k)([e]) != 0. In particular

    k = 1 + floor(log_p(n m'))                           (7)

always suffices. Formula (7) is computed with integer comparisons, not
floating-point logarithms. For the zero matrix no such detection is claimed.

Consequences: if a proposed reverse-product defect is a nonzero matrix
idempotent supported in H, (4) and (6) reject it at a bounded precision.
If f<e are nested idempotents in M_n(F_p[H]), apply the bound to e-f.
No isomorphism e F_p[G]^n ~= f F_p[G]^n, even after a common projective
stabilization, is possible. Neither inverse factor is assumed to be
supported in H.

## 4. The bound can be necessary even for scalar idempotents

Fix p and r >= 1. Take H=C_m with m=p^r+1 and N=sum_(g in H) [g]. In
F_p[H] define e=1-m^(-1)N. The identity N^2=mN shows e^2=e, and e is
nonzero because m>1 and its nonidentity coefficients are nonzero.
Over Z_p[H], the same expression E=1-N/m is an idempotent lift with

    t_p([e]) = 1-1/m = p^r/(p^r+1).                    (8)

Its p-adic valuation is exactly r. Therefore every residue t_(p,k)([e])
with k<=r vanishes, but t_(p,r+1)([e]) is nonzero. Here n=1 and m'=m, so
(7) gives exactly r+1. The uniform bound is attained by this family.

Thus no fixed precision can detect every nonzero scalar idempotent, even
among finite cyclic groups. These examples are **not** inverse defects or
counterexamples to direct finiteness: their nonzero higher lifted trace
proves precisely that they cannot be reverse-product defects in any ambient
group algebra containing H.

## What is still missing

To prove the full conjecture one must exclude every nonzero d=I-BA when
AB=I for arbitrary groups and fields. This argument excludes the specified
finite-subgroup class and any other d with a computed nonzero trace residue.
It supplies no detection bound, trace-faithfulness theorem, or substitute
invariant for all remaining projectives. Increasing precision or passing
finite tests cannot be presented as a proof that those projectives vanish.

The follow-up [full-proof gap audit](../../notes/KAPLANSKY_FULL_PROOF_GAP_AUDIT_2026-09-07.md)
proves the exact general-ring equivalence between stable finiteness and
vanishing of projectives with zero K_0 class. It also gives a finite-group
counterexample to injectivity of the entire lifted-trace invariant on K_0,
and checks the finite-support and completion gaps. The equivalence identifies
the missing assertion; it does not establish it for arbitrary group algebras.

## Exact replay and integration

`experiments/kaplansky_trace_certificate.py` uses integer arithmetic only.
It validates a finite group's multiplication table, lifts matrix idempotents,
checks idempotence and reduction exactly, and compares each resulting trace
with an independently computed regular-representation rank over F_p.
The JSON input consists of `group.table`, `group.identity`, prime `p`,
positive `precision`, positive `matrix_size`, and lists `e` and `f` of
`[row, column, group_index, coefficient]` terms. Repeated terms are added;
zero terms are removed. The two input matrices have the same specified size.
The committed certificate includes complete examples of this format.

The output is either `obstructed` (different lifted traces) or `inconclusive`
(equal traces). It never reports equivalence or direct finiteness from an
equal trace. Its finite table alone does not certify an embedding into Q;
the existing Cairn claim `leavitt-trace-balanced-nested-idempotents` supplies
that embedding for the C_3 x C_3 example.

Reproduce and verify the 17 certificates:

```sh
python3 experiments/kaplansky_trace_certificate.py --examples \
  --output research/artifacts/kaplansky-trace-certificates.json
python3 experiments/kaplansky_trace_certificate.py \
  --verify research/artifacts/kaplansky-trace-certificates.json
python3 -m unittest discover -s experiments \
  -p 'test_kaplansky_trace_certificate.py' -v
```

The regressions include the known Leavitt pair (inconclusive modulo two,
separated modulo four), the sharp scalar families at p=2 and p=3, all 64
elements of F_2[S_3] screened for idempotence, noncommuting matrix examples,
arbitrary coefficient lifts, equal-trace negative controls, malformed input,
and tampered certificates. The exhaustive 64-element test validates only
this finite regression universe, not the general theorem.

`.github/workflows/kaplansky-trace.yml` runs these tests, exact replay, and
deterministic regeneration on relevant pushes and pull requests. The Cairn
route `leavitt-balanced-corners-finite-trace-proof` connects the general
invariant to the existing corner refutation. The theorem is proved in prose;
these files add no Lean theorem and make no Lean kernel-verification claim.
