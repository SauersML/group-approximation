---
rg: 2
id: stw64-z-scales-rc-offset-proof
kind: route
title: Softness, the supersoft majorant and the gap formula pin every Jiang-Su versus supersoft comparison
target: stw64-z-scales-rc-below-supersoft
requires:
  - stw64-supersoft-calculus
  - stw64-supersoft-gap-is-comparison-radius
artifacts:
  - research/artifacts/stw64-z-scales-rc-offset-2026-09-16.md
---

Full details are in Section 2 of the artifact. Robert (Section 6.3) gives
the relations in Cu(Z) used below:

- n+t'=(n+t)';
- n<=t' iff n<t;
- t'<=n iff t<=n;
- t'<<r' iff t<r;
- t'=sup_{r<t} r'.

**Elementary inputs.** None of these uses a required claim.

- (R) Ranks. For every functional lambda and finite t>0,
  lambda(f(t'))=t*lambda(u). Take n large and m=ceil(nt). Cu(Z) gives
  (m-1)<=(nt)'<=m. Apply f and lambda, then divide by n. Hence f(t')-hat
  equals t*u-hat.
- (S) Softness. Let v<<f(t'). Then v<=f(r') for some r<t, because
  f(t')=sup_{r<t} f(r'). Choose k with (k+1)r<=kt. Then (k+1)v<=k*f(t').
- (NC) Neither f(t') nor s_c is compact. At a normalized quasitrace each
  has finite positive rank, so x<<x together with softness would give
  (k+1)x<=kx, which is impossible.
- (U) The admissible constants for the rc infimum form an upward-closed
  set. So every finite R>rc(A) is admissible.

**The calculus claim supplies:** alpha preserves order and increasing
suprema; s_c has rank c*u-hat and is soft; every soft x satisfies
x<=alpha(x-hat); and x+s_c=alpha(x-hat+c*u-hat). The last identity gives
s_p+s_q=s_{p+q}.

**The gap claim supplies (G):** s_a<<s_b implies rc(A)<=b-a.

**Proof of (a).** If b<=a, then (S), the majorant and (R) give
f(b')<=alpha(b*u-hat)=s_b<=s_a. The converse follows by evaluating a
normalized quasitrace.

**Proof of (e), and hence (b).** Put x=sum_i f_i(a_i') and r=sum_i a_i.

- *If r-d>rc(A).* By (R) the rank of x is the rank of s_d plus
  (r-d)*u-hat. By (U), s_d<=x.
- *If r-d=rc(A)<infinity.* Take d_j increasing to d. Then s_{d_j}<=x for
  every j, and s_d=sup_j s_{d_j}<=x.
- *Converse.* Suppose s_d<=x, and let eta>0. Morphisms and finite sums
  preserve <<, so x<<x_eta:=sum_i f_i((a_i+eta)'). By (a) and additivity,
  x_eta<=s_{r+k*eta}, so s_d<<s_{r+k*eta}. Here k is the number of
  morphisms. Evaluating a normalized quasitrace on s_d<=x gives d<=r, so
  d<r+k*eta. (NC) also excludes equality, but it is not needed here.
  (G) then gives rc(A)<=r+k*eta-d. Letting eta tend to 0
  gives r-d>=rc(A). If rc(A)=infinity this is a contradiction, so s_d<=x
  is impossible.

**Proof of (c).** Suppose b-a>rc(A). Pick b'' with a+rc(A)<b''<b. Then
s_a<=f(b'')<<f(b').

Conversely, f(b')=sup_{b_k<b} f(b_k'). So s_a<<f(b') gives s_a<=f(b_k')
for some b_k<b, and (b) gives b-a>b_k-a>=rc(A).

**Proof of (d).** If b<a, then f(b')<<f(a')<=s_a.

Conversely, s_a=sup_{a_k<a} s_{a_k}. So f(b')<<s_a gives f(b')<=s_{a_k}
for some a_k<a, and (a) gives b<a.

**Invisibility.** The addition table follows from (R) and absorption.
The relations not already covered by (a)-(d) are these.

- `nu<=f(t')` iff n<t. The "if" direction is the image of n<=t' in
  Cu(Z). For "only if", ranks give n<=t. Equality is excluded because nu
  is compact and f(t')=sup_{r<t} f(r').
- `nu<=s_c` iff n<c. If n<c, absorption gives s_c=nu+s_{c-n}. The
  converse holds as in the previous item, using s_c=sup_{c_j<c} s_{c_j}.
- `s_c<=nu` iff n-c>=rc(A). If s_c<=nu, then s_c<=f((n+eta)') for every
  eta>0, so (b) gives n-c>=rc(A). Conversely, if n-c>=rc(A), then
  s_c<=f(n')<=nu.
- `f(t')<<f(r')` iff t<r. For "only if", ranks give t<=r, and (NC)
  excludes t=r.
- Relations with compact labels: x<<nu iff x<=nu, and nu<<y iff nu<=y.
- Relations with the top: in the simple algebra A the top sup_n nu
  dominates everything. A label is compactly contained in it iff the label
  lies below some mu. For s_c this happens iff rc(A)<infinity, by the
  previous item.

Here nu denotes n*[1_A].

The relations among the s_c alone do not involve f. So every table entry
is independent of f.
