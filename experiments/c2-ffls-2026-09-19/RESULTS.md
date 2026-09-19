# c2-ffls-2026-09-19 (w18-048)

Supports `research/c2-character-bound-excludes-cyclic-edge-level-splittings.md`. The group is
`H = <b,c,d,e | eDDEdd.bCB.eDDEdd.bDcBd>`, `eps = (3,0,1,1)`, inside `F_4 x|_phi Z`, `phi: p->q->r->s->rrSqPRs`.

## Files

- `chars.py`: exact (sympy) abelianised Fox derivatives, and `Delta_omega` as the gcd over `t` of the specialised derivatives.
- `delta.py`: exact coset-image test for the `D_N[t^+-1]` torsion degree. It needs `hlib.py` (word utilities, `eps`, `toxy`) and `fbc.py` (`tofib`, the normal form in the fibre `F_4`).
- `twisted.py`, `run.py`: twisted-Alexander torsion over transitive permutation reps. These are a code check only, since the bi-monic test is vacuous (D1).
- `fold2.py`: a Stallings-folding helper that `hlib.py` imports.

## Output

`python3 chars.py`:

```
b (D - 1)/D | at D=1: 0
c -B*(D - 1)/(C*D) | at D=1: 0
d -(B*D + C*D*E - 2*C*D + C*E - C + D*E - D + E - 1)/(C*D**2) | at D=1: (-B - 2*C*E + 3*C - 2*E + 2)/C
e (C + 1)*(D - 1)*(D + 1)/(C*D**2) | at D=1: 0
on S: 5*t - 1  1/omega(d) = 1/5   off S: 1
on S: 5*t - 4  1/omega(d) = 4/5   off S: 1
on S: 5*t - 4  1/omega(d) = 4/5   off S: 1
on S: 3*t - 2  1/omega(d) = 2/3   off S: 1
```

`python3 delta.py`. The images of `(PC)^-1 d_x r` in `Q[<u>\H]` are all nonzero, so the `D_N` torsion degree is 0:

```
b terms 4 nonzero cosets 2 {'SqpQsRqrSqPRSrpQsR': -1, 'SqpQsRqrSqPRSr': 1}
d terms 10 nonzero cosets 10
e terms 4 nonzero cosets 4 {...}
```

`python3 twisted.py 3` and `python3 twisted.py 4` ran over 258 and 12208 reps, giving 10 and 35 distinct orders. The cyclotomic factors are consistent with the c-block bound, since `Delta_rho` divides `charpoly(rho(u))` and so has degree at most n. The large non-bi-monic factors in the raw n=4 output have degree 16-19 > 4. So they are artifacts of the random-minor gcd (too few trials), not factors of `Delta_rho`. This is moot anyway because of D1.

## Verification tier

- The Fox derivatives, `Delta_omega` on and off `S`, and the coset images are exact.
- Everything else is a hand proof in the `-proof` node.
