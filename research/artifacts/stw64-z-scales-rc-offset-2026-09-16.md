# STW LXIV: unital Jiang--Su scales are comparison-radius rigid

Date checked: 2026-09-16. Everything here is derived from published inputs.
It does not claim priority, does not solve a named open problem, and asserts
no Lean formalization.

## Status gate

The following sources were fetched as arXiv HTML and converted to text in
this session.

- Schafhauser--Tikuisis--White, *Nuclear C\*-algebras: 99 problems*,
  arXiv:2506.10902v2, Problems LXIII and LXIV. Problem LXIV asks: "What is the
  Cuntz semigroup of the Villadsen/Toms counterexamples to classification
  with stable rank one, and in particular, do there exist two distinct Cuntz
  semigroup morphisms from Cu(Z) into these Cuntz semigroups?" The same
  section says the Villadsen-type counterexamples of Toms all contain unital
  copies of Z.
- Gardella--Perera, *The modern theory of Cuntz semigroups of C\*-algebras*,
  arXiv:2212.02290v2, Problems 16.1--16.3. Problem 16.3 asks for "two
  distinct Cu-morphisms Cu(Z)->Cu(A) preserving unit classes".
- Elliott--Niu, *Remarks on Villadsen algebras, II*, arXiv:2510.13695v2.
  They compute the comparison-radius *function* r_infinity as a Cu-invariant
  of UHF- and AF-Villadsen algebras. They also write: "The question of what the
  structure of the Cuntz semigroup for Villadsen algebras actually is is
  clearly of considerable interest."
- Antoine--Perera--Robert--Thiel, *C\*-algebras of stable rank one and their
  Cuntz semigroups*, arXiv:1809.03984v3, Definition 8.1, Proposition 8.2,
  Theorem 8.4 and 8.6. Paragraph 8.6 restates Toms's radius of comparison
  in Cuntz-semigroup form.

None of these sources settles either question of Problem LXIV. This is a
targeted check, not an exhaustive literature certification.

The web-search budget for this session ran out before a prior-art check of
the shift metric in Section 1 (Proposition 1.2) could be made. Similar
shift-type distances on Cu-morphisms occur in classification of
homomorphisms out of C_0(0,1]. The references Ciuperca--Elliott
(arXiv:0707.2220) and Robert--Santiago (arXiv:0905.0680) exist with those
titles and topics, but their shift-distance content is **unverified here**.
No novelty is claimed for Section 1 or Section 2.

## 0. Notation and two elementary facts

Robert computes Cu(Z) in Section 6.3 of the paper the repository already
imports in `stw63-strict-comparison-cu-collapse-proof`:

    Cu(Z) = N  disjoint union  (0,infinity].

Write n for the compact integer classes and t' for the soft classes. The
standard relations are:

- n+t' = (n+t)' and t'+r' = (t+r)';
- n <= t' iff n<t, and t' <= n iff t<=n;
- t' <= r' iff t<=r, and t' << r' iff t<r (for finite t);
- t' = sup_{r<t} r' along any increasing sequence r_k to t;
- the top element infinity is sup_n n.

A *unital morphism* is a Cu-morphism f:Cu(Z)->S=Cu(A) with f(1)=u=[1_A].
A Cu-morphism preserves 0, addition, order, suprema of increasing sequences
and <<. Write f(t') for the image of a soft class. Then f(n)=nu, and
f(infinity)=sup_n nu does not depend on f.

**Fact 0.1 (ranks).** Let lambda be any functional on S and t>0 finite. Then
lambda(f(t'))=t*lambda(u).

*Proof.* For n large, put m=ceil(nt)>=2. Since m-1<nt<=m, Cu(Z) gives
m-1<=(nt)'<=m. Apply f to get (m-1)u <= n f(t') <= mu, and then apply lambda.
If lambda(u)=0 then both sides vanish. If lambda(u)=infinity then
lambda(f(t'))=infinity. Otherwise divide by n and let n tend to infinity.
QED

**Fact 0.2 (softness).** f(t') is soft: for every v<<f(t') there is k with
(k+1)v<=k f(t').

*Proof.* Since f(t')=sup_k f(r_k') with r_k increasing to t, some r<t has
v<=f(r'). Choose k with (k+1)r<=kt. Then
(k+1)v <= f(((k+1)r)') <= f((kt)') = k f(t'). QED

**Radius of comparison.** APRT 8.6 defines rc(A) as the infimum of the
r in (0,infinity] such that

    lambda(x)+r <= lambda(y) for all lambda in F_u(Cu(A))   implies   x<=y

for all x,y in Cu(A). Here F_u consists of the functionals with lambda(u)=1.
Call such an r *admissible*. Enlarging r weakens the hypothesis, so the
admissible set is upward closed. Hence **every finite R>rc(A) is
admissible.**

## 1. Pairwise rigidity; any unital A

**Theorem 1.** Let A be unital and f,h unital morphisms Cu(Z)->Cu(A). Let
0<a<=b<infinity with b-a>=rc(A). Then

    h(a') <= f(b').

*Proof.* Suppose first b-a>rc(A). Put R=b-a, which is admissible. By Fact 0.1,
every lambda in F_u satisfies lambda(h(a'))+R = a+R = b = lambda(f(b')), so
h(a')<=f(b').

If instead b-a=rc(A), choose a_k increasing to a. Each pair satisfies
b-a_k>rc(A), so h(a_k')<=f(b'). Hence h(a')=sup_k h(a_k')<=f(b'). QED

**Corollary 1.1 (zero radius).** If rc(A)=0, all unital morphisms
Cu(Z)->Cu(A) coincide.

*Proof.* Theorem 1 with a=b gives h(a')<=f(a'), and symmetrically. The compact
classes and infinity have the same image under both maps. QED

This is the Cu-level core of `stw63-strict-comparison-cu-collapse-proof`.
Here the hypothesis is rc(A)=0, and neither stable rank one nor simplicity is
used. The relation between rc(A)=0 and strict comparison is not needed and is
not asserted.

**Definition.** For unital morphisms f,h, define

    delta(f,h) = inf { R>=0 : h(a')<=f((a+R)') and f(a')<=h((a+R)')
                              for every finite a>0 }.

The infimum of the empty set is infinity.

**Proposition 1.2.**

1. The infimum is attained when it is finite, and the admissible set of R is
   upward closed.
2. delta(f,h) <= rc(A).
3. delta(f,h)=0 iff f=h.
4. delta is symmetric and satisfies delta(f,k)<=delta(f,h)+delta(h,k).

Thus the unital morphisms Cu(Z)->Cu(A) form an extended metric space of
diameter at most rc(A).

*Proof.*

(1) If R works and R''>=R, then h(a')<=f((a+R)')<=f((a+R'')'). Suppose
R_k works and decreases to R_0. Fix a and a''<a. Pick k with
R_k<=R_0+(a-a''). Then

    h(a'') <= f((a''+R_k)') <= f((a+R_0)').

Taking the supremum over a'' increasing to a gives h(a')<=f((a+R_0)'). The
other inequality is symmetric.

(2) If rc(A) is finite, R=rc(A) works by Theorem 1 with b=a+rc(A).

(3) If R=0 works, then h(a')<=f(a')<=h(a') for all a, so f=h as in
Corollary 1.1. The converse is trivial.

(4) Symmetry is built into the definition. Suppose h(a')<=f((a+R_1)') for
all a, and f(r')<=k((r+R_2)') for all r. Then

    h(a') <= f((a+R_1)') <= k((a+R_1+R_2)').

The reverse inequality is obtained in the same way. QED

**Corollary 1.3 (disagreement is a germ at zero).** Suppose f(a')=h(a') for
every a in (0,epsilon), for some epsilon>0. Then f=h. Equivalently, if
f(a')!=h(a') then f((a/k)')!=h((a/k)') for every integer k>=1.

*Proof.* Every finite t>0 is a finite sum of values below epsilon, and both
maps are additive. QED

Suppose moreover that Cu(A) has weak cancellation, i.e. x+z<=y+z' and z'<<z
imply x<=y. This holds for stable rank one. Since nu<<nu, for each integer
n>=0 separately, f(a')=h(a') holds iff f((a+n)')=h((a+n)'). (APRT 2.5 and
the remark after its lemma give cancellation of compact elements from weak
cancellation.)

## 2. Exact offset below the supersoft scale; stable rank one

Now let A satisfy the hypotheses of `stw64-supersoft-calculus`: separable,
simple, unital, infinite-dimensional, stable rank one, with nonempty
normalized 2-quasitrace space. Put s_c = alpha(c*u-hat) for finite c>0. The
imported calculus gives the following facts.

- (C1) s_c has rank c*u-hat, is soft, and alpha preserves order and
  suprema of increasing sequences. So s_{c_k} increases to s_c when c_k
  increases to c.
- (C2) Every soft x satisfies x<=alpha(x-hat).
- (C3) x+s_c = alpha(x-hat+c*u-hat) for every x.
- (C4) Weak cancellation holds, and every finite R>rc(A) is an admissible
  comparison constant for x-hat+R*u-hat<=y-hat.

The imported gap claim `stw64-supersoft-gap-is-comparison-radius` gives

- (G) s_a<<s_b implies rc(A)<=b-a.

**Fact 2.0.** No nonzero element x with 0<tau(x)<infinity for a normalized
quasitrace tau is both soft and compact. Indeed, x<<x and softness give
(k+1)x<=kx, which contradicts the rank.

**Theorem 2.** Let f be any unital morphism Cu(Z)->Cu(A), and let a,b,c,d>0
be finite.

- (a) f(b') <= s_a iff b<=a.
- (b) s_a <= f(b') iff b-a>=rc(A). If rc(A)=infinity this never holds.
- (c) s_a << f(b') iff b-a>rc(A).
- (d) f(b') << s_a iff b<a.
- (e) More generally, let f_1,...,f_k be unital morphisms, possibly
  distinct, and put x=sum_i f_i(a_i') with r=sum_i a_i. Then
  s_d<=x iff r-d>=rc(A).

In particular, for R<rc(A) no finite t has s_t<=f((t+R)'). The minimum
shift carrying the supersoft scale below a unital Jiang--Su scale is
exactly rc(A), for every such scale and at every level t.

*Proof.*

(a) If b<=a, Fact 0.2 and (C2) give f(b')<=alpha(b*u-hat)=s_b<=s_a. The
converse follows by evaluating a normalized quasitrace.

(e), and hence (b) as the case k=1. First suppose r-d>rc(A). By Fact 0.1 and
(C1), the rank of s_d plus (r-d)*u-hat equals the rank of x, so s_d<=x by
(C4). If r-d=rc(A), take d_j increasing to d. Then s_{d_j}<=x for every j, so
s_d<=x by (C1).

Conversely, suppose s_d<=x, and let eta>0. Then
x << x_eta := sum_i f_i((a_i+eta)'), since << is preserved by f_i and by
finite sums. By (a) and (C3),

    x_eta <= sum_i s_{a_i+eta} = s_{r+k*eta}.

Here (C3) applies with x=s_p, since s_p+s_q=alpha((p+q)u-hat)=s_{p+q}. So
s_d<<s_{r+k*eta}. Ranks force d<=r<r+k*eta. (Fact 2.0 would also exclude
d=r+k*eta, but strictness already follows from eta>0.) So (G) applies and
gives rc(A)<=r+k*eta-d. Let eta tend to 0. If
rc(A)=infinity, the argument shows that s_d<=x is impossible.

(c) If b-a>rc(A), choose b'' with a+rc(A)<b''<b. Then
s_a<=f(b'')<<f(b') by (b). Conversely, f(b')=sup_k f(b_k') with b_k
increasing to b, so s_a<<f(b') forces s_a<=f(b_k') for some b_k<b. By (b),
b-a>b_k-a>=rc(A).

(d) If b<a, then f(b')<<f(a')<=s_a. Conversely, s_a=sup_k s_{a_k} with a_k
increasing to a, so f(b')<<s_a gives f(b')<=s_{a_k} for some a_k<a. By (a),
b<=a_k<a. QED

**Corollary 2.1 (the canonical scales cannot see which map was used).** Fix
the formal labels 0, n (integers), t' (finite t>0), [s_c] (finite c>0) and
infinity. For a unital morphism f, evaluate them as 0, nu, f(t'), s_c and
top. The following are the same for every unital morphism f.

- The addition table on labels:
  - nu+f(t')=f((n+t)');
  - f(t')+f(r')=f((t+r)');
  - f(t')+s_c=s_{t+c}, by (C3) and Fact 0.1;
  - nu+s_c=s_{n+c};
  - s_c+s_d=s_{c+d}.
- Every relation <= and << between two evaluated labels.

Explicitly:

- nu<=f(t') iff n<t;
- f(t')<=nu iff t<=n;
- nu<=s_c iff n<c;
- s_c<=nu iff n-c>=rc(A);
- f(t')<=s_c iff t<=c;
- s_c<=f(t') iff t-c>=rc(A);
- s_c<<f(t') iff t-c>rc(A);
- f(t')<<s_c iff t<c;
- f(t')<<f(r') iff t<r;
- f(t')<<nu iff t<=n.

The relations among the s_c do not involve f.

*Proof of the relations not already in Theorem 2.*

- nu<=f(t') forces n<=t by rank. If n=t, then nu<<nu<=f(t')=sup_{r<t} f(r')
  gives nu<=f(r') with r<n, which is impossible.
- If n<c, (C3) gives s_c=nu+s_{c-n}. If nu<=s_c with n>=c, then
  nu<<nu<=sup_j s_{c_j} with c_j<c<=n, which contradicts rank.
- s_c<=nu<=f((n+eta)') gives n+eta-c>=rc(A) by Theorem 2(b), for every
  eta>0. Conversely, if n-c>=rc(A), then s_c<=f(n')<=nu.
- f(t')<<f(r') with t>=r would make f(t') compact, which Fact 2.0 excludes.
- If t<=n, then f(t')<=nu<<nu. The converse holds by rank.

A label is compactly contained in infinity iff it lies below some mu. For
[s_c] this happens iff rc(A)<infinity, independently of f. QED

## 3. Consequences for LXIV and LXIII

Let f!=h be a hypothetical Gardella--Perera pair in a separable, simple,
unital, stable-rank-one target A.

1. 0<delta(f,h)<=rc(A). In particular rc(A)>0, by Corollary 1.1. This is
   the Cu-level core of `stw63-strict-comparison-cu-collapse-proof`. The
   2026-09-04 obstruction is a different statement: it excludes the
   canonical supersoft scale as a morphism when rc(A)>0.
2. f and h already disagree at arbitrarily small soft levels. With weak
   cancellation, they also disagree at every integer translate of a
   disagreement level.
3. The difference cannot be detected by comparing values of one morphism
   with integers or with the canonical supersoft classes s_c. It also cannot
   be detected by comparing an s_d with a finite sum of values of possibly
   different unital morphisms (Theorem 2(e)). Mixed comparisons between
   values of two different morphisms are not covered.
4. Any detection must use one of two things:
   - a mixed comparison h(a')<=f(b') inside the window 0<=b-a<rc(A);
   - a comparison with a class outside the canonical scalar scales, such as
     a class whose rank is nonconstant, a projection, or a twisted soft class
     that is not of the form alpha(c*u-hat).
5. Remark, not proved here: after composing with the first-factor map
   A->A⊗Z, one expects the two maps to agree, by the strict-comparison
   collapse applied in the Z-stable algebra. The known soft order-reflection
   theorem for the first-factor map assumes almost unperforation, so it does
   not apply when rc(A)>0.

## 4. Scope

Nothing here computes Cu(A) for a Villadsen or Toms algebra. Nothing here
decides whether a second unital morphism exists. The results only say where
a difference can live and rule out some detectors of it.
