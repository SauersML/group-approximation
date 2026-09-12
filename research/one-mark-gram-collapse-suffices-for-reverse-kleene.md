---
rg: 2
id: one-mark-gram-collapse-suffices-for-reverse-kleene
kind: claim
title: One collapsing mark-Gram microstate sequence suffices for reverse Kleene
distinct_from:
  canonical-profile-kleene-higman: that assumes every full canonical-profile microstate sequence collapses the mark; this needs only one sequence under hypothetical hyperlinearity and only the finite Gram moments of the mark support.
  group-algebra-mark-reverse-kleene-collapse: that uses a universal sequence quantifier and finitely specified canonical side tests; this isolates the logically minimal existential canonical-profile endpoint.
  depthwise-canonical-kleene-needs-no-uniform-runtime-gap: that supplies a practical universal estimate implying collapse on every canonical sequence; this is the weaker endpoint such an estimate may target.
---

**ESTABLISHED.**  Suppose a total computable compiler sends every machine
index `e` to a finite alphabet, a uniformly recursively enumerable
presentation `Gamma_e=<S_e|R_e>`, and

```text
p_e=sum_(i=1)^m c_i w_i in Q[Gamma_e],                 (MGC1)
```

and assume

```text
e halts => p_e!=0 in Q[Gamma_e].                        (MGC2)
```

For a fixed `e`, call a matrix sequence `U_n` **mark-Gram canonical** when,
for the finitely many support words in `(MGC1)`,

```text
tr_d_n(w_i(U_n)^*w_j(U_n))
  -> tau_(Gamma_e)(w_i^*w_j)                            (MGC3)
```

for all `i,j`.  Assume the following NONHALT endpoint:

```text
e nonhalts and Gamma_e is hyperlinear
  => there exists one mark-Gram canonical microstate sequence U_n
     with liminf_n ||p_e(U_n)||_2=0.                    (MGC4)
```

Then one can effectively construct a finitely presented nonhyperlinear
group.

This is the minimal canonical-profile content of the algebra-mark reverse
Kleene argument:

* collapse need not hold for **every** canonical microstate sequence;
* no computable choice of the collapsing sequence or convergence rate is
  needed;
* no canonical moments outside the finite support of `p_e^*p_e` are used;
* `liminf=0` is enough—full convergence to zero is unnecessary.

For applications, a universal finite-depth estimate remains a natural way to
prove `(MGC4)`.  But the endpoint itself asks only for one hypothetical
hyperlinear approximation whose mark norm has a zero subsequential limit.
It is strictly semantic and must not be replaced by `p_e=0`; the latter is
ruled out by `exact-group-algebra-death-cannot-code-nonhalting`.
