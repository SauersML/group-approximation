#!/usr/bin/env python3
"""Compute the Cartan-type stabilizer and its level-16 Mackey cocycle."""

from collections import Counter, deque
import json


def mm(a, b, mod):
    return tuple(
        sum(a[3*i+k] * b[3*k+j] for k in range(3)) % mod
        for i in range(3) for j in range(3)
    )


def eye():
    return (1,0,0,0,1,0,0,0,1)


def elem(i, j, t, mod):
    a = list(eye()); a[3*i+j] = t % mod; return tuple(a)


def gf2_solve(rows, rhs, n):
    aug = [sum((bit & 1) << j for j, bit in enumerate(row)) | ((b & 1) << n)
           for row, b in zip(rows, rhs)]
    pivots = []
    r = 0
    for c in range(n):
        p = next((i for i in range(r, len(aug)) if (aug[i] >> c) & 1), None)
        if p is None: continue
        aug[r], aug[p] = aug[p], aug[r]
        for i in range(len(aug)):
            if i != r and ((aug[i] >> c) & 1): aug[i] ^= aug[r]
        pivots.append(c); r += 1
    mask = (1 << n) - 1
    if any((x & mask) == 0 and ((x >> n) & 1) for x in aug): return None, []
    particular = [0] * n
    for i, c in enumerate(pivots): particular[c] = (aug[i] >> n) & 1
    free = [c for c in range(n) if c not in pivots]
    basis = []
    for f in free:
        v = [0] * n; v[f] = 1
        for i, c in enumerate(pivots): v[c] = (aug[i] >> f) & 1
        basis.append(v)
    return particular, basis


def addv(a, b): return [x ^ y for x, y in zip(a, b)]


def gf2_rank(rows, n):
    rows = [sum((x & 1) << j for j, x in enumerate(row)) for row in rows]
    rank = 0
    for c in range(n):
        p = next((i for i in range(rank, len(rows)) if (rows[i] >> c) & 1), None)
        if p is None: continue
        rows[rank], rows[p] = rows[p], rows[rank]
        for i in range(len(rows)):
            if i != rank and ((rows[i] >> c) & 1): rows[i] ^= rows[rank]
        rank += 1
    return rank


def main():
    gens4=[]; gens16=[]; inv16=[]
    for i in range(3):
        for j in range(3):
            if i != j:
                gens4.append(elem(i,j,1,4)); gens16.append(elem(i,j,1,16)); inv16.append(elem(i,j,-1,16))
    e4=eye(); e16=eye()
    lifts={e4:(e16,e16)}; q=deque([e4])
    while q:
        x=q.popleft(); lx,lxi=lifts[x]
        for g4,g16,gi16 in zip(gens4,gens16,inv16):
            y=mm(g4,x,4)
            if y not in lifts:
                lifts[y]=(mm(g16,lx,16),mm(lxi,gi16,16)); q.append(y)
    X=(1,0,0,0,3,0,0,0,0)
    stab=[]
    for g,(lg,lgi) in lifts.items():
        # inverse mod4 is reduction of tracked inverse lift
        gi=tuple(v%4 for v in lgi)
        if mm(mm(g,X,4),gi,4)==X: stab.append(g)
    idx={g:i for i,g in enumerate(stab)}
    orders=[]
    for g in stab:
        y=e4
        for o in range(1,65):
            y=mm(y,g,4)
            if y==e4: orders.append(o); break
    abelian=all(mm(g,h,4)==mm(h,g,4) for g in stab for h in stab)
    equations=[]; exps=[]; exp_pair={}
    for g in stab:
        for h in stab:
            gh=mm(g,h,4); row=[0]*len(stab)
            row[idx[g]]+=1; row[idx[h]]+=1; row[idx[gh]]-=1
            lg,_=lifts[g]; lh,_=lifts[h]; _,lih=lifts[gh]
            c=mm(mm(lg,lh,16),lih,16)
            Y=tuple(((c[i]-(1 if i in (0,4,8) else 0))//4)%4 for i in range(9))
            exp=sum(X[3*i+j]*Y[3*j+i] for i in range(3) for j in range(3))%4
            equations.append(row); exps.append(exp)
            exp_pair[(idx[g],idx[h])]=exp
    rows2=[[x&1 for x in row] for row in equations]
    p,basis=gf2_solve(rows2,[x&1 for x in exps],len(stab))
    trivial=False; nullity=None
    if p is not None:
        nullity=len(basis)
        for mask in range(1<<len(basis)):
            z=p[:]
            for j,v in enumerate(basis):
                if (mask>>j)&1: z=addv(z,v)
            residual=[((e-sum(a*x for a,x in zip(row,z)))//2)&1 for row,e in zip(equations,exps)]
            t,_=gf2_solve(rows2,residual,len(stab))
            if t is not None:
                trivial=True; break
    # The stabilizer is elementary abelian.  Choose a group basis and compute
    # the alternating commutator bicharacter of the scalar cocycle.
    span={e4}; hbasis=[]
    for g in stab:
        if g not in span:
            hbasis.append(g)
            span |= {mm(x,g,4) for x in list(span)}
    bichar=[]
    for g in hbasis:
        row=[]
        for h in hbasis:
            row.append(((exp_pair[(idx[g],idx[h])]-exp_pair[(idx[h],idx[g])])//2)&1)
        bichar.append(row)
    brank=gf2_rank(bichar,len(hbasis))
    out={
      "group_order":len(lifts), "stabilizer_order":len(stab), "abelian":abelian,
      "element_order_distribution":dict(sorted(Counter(orders).items())),
      "mackey_cocycle_exponent_distribution":dict(sorted(Counter(exps).items())),
      "mod2_solution_nullity":nullity, "mackey_cocycle_is_coboundary_mu4":trivial,
      "stabilizer_f2_rank":len(hbasis), "commutator_bicharacter_matrix":bichar,
      "commutator_bicharacter_rank":brank,
      "minimal_projective_irrep_dimension":2**(brank//2),
    }
    print(json.dumps(out,sort_keys=True))


if __name__=="__main__": main()
