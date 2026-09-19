# From a bounded-width word certificate to a non-weakly-sofic group

Former Cairn route `non-weakly-sofic-from-word-certificate`, demoted with the
off-program landmark it served.

Let `F = F(s_1,...,s_r)` and `g_1,...,g_k,x in F` be the certificate, and put

```text
N_0 := N(g_1,...,g_k)      the normal closure of the g_i in F.
```

Certificate condition (2) is verbatim the assertion

```text
x  in  closure_prof( [g_1]^F [g_2]^F ... [g_k]^F ),
```

by the finite-quotient characterization of profinite closure.  Every `g_i`
lies in `N_0` and certificate condition (1) says `x not-in N_0`.  So the
containment demanded by `glebsky-rivera-w-sofic-criterion` fails for `N_0`
at the single sequence `g_1,...,g_k`, and

```text
G = < s_1,...,s_r | g_1,...,g_k >  =  F/N_0
```

is not weakly sofic.  It is finitely presented by construction, which is why
this route also discharges `non-weakly-sofic-finitely-presented-reduction`
without extra work in the direction that matters for building an example.

**The presented group is `F/N_0`, not `F/N` for any larger `N`.**  This is the
step worth stating, because it is where a construction gets its finite
presentation for free: the certificate is about a fixed finite list, so one
may simply present on that list and forget whatever larger normal subgroup
motivated it.  Enlarging `N_0` to any `N` containing it preserves the closure
membership (which depends only on `F,x,g_1,...,g_k`) but risks swallowing
`x`, so the minimal choice is the correct one.
