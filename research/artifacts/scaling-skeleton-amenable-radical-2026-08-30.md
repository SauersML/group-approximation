# Scaling-skeleton amenable-radical invariant

Date: 2026-08-30

Let `E_m` be the eight-generator scaling-family presentation and
`N_m=<<c_m>>` the normal closure of the lamp generator.  Killing `c_m`
makes the marked word and all its centrality relators trivial.  The remaining
presentation is the ascending HNN extension of

```text
B ~= Z^3 semidirect SL_3(Z)
```

along `alpha_m(a,s)=(ma,s)`.  Direct-limit normal form gives

```text
E_m/N_m ~= V_m
 := Z[1/m]^3 semidirect (SL_3(Z) x Z),
```

where `(s,k)` acts by `a |-> m^k s(a)`.

Put `A_m=Z[1/m]^3` and `R_m=A_m semidirect_m Z`.  This group is solvable
and normal, with quotient `V_m/R_m~=SL_3(Z)`.  Margulis's normal subgroup
theorem, used only for this irreducible higher-rank lattice, implies that the
amenable radical of `SL_3(Z)` is trivial.  Therefore

```text
Rad_am(V_m)=R_m.
```

Writing `t` for the `Z` generator gives
`[t,a]=(m-1)a`, whence

```text
R_m^ab ~= Z direct_sum (A_m/(m-1)A_m)
        ~= Z direct_sum (Z/(m-1)Z)^3.
```

Localization at `m` does not change reduction modulo `m-1` because the
two integers are coprime.  Thus

```text
|Tor(Rad_am(V_m)^ab)|=(m-1)^3.
```

The invariant recovers `m` from the abstract quotient.  No normal-subgroup
claim about the full group `E_m` is imported.
