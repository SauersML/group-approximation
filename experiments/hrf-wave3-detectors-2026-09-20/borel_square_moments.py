"""Exact mod-5 moment test on the400-point Borel-square cover of PSL2(19)^2."""
import json
from pathlib import Path
from flint import nmod_mat

q=19
p=5
xs=[(2,11,16,3),(5,11,4,9),(6,15,12,8)]
y=(1,8,12,6)

def act(m,t):
    a,b,c,d=m
    if t==q:
        return a*pow(c,-1,q)%q if c else q
    den=(c*t+d)%q
    return (a*t+b)*pow(den,-1,q)%q if den else q

def orbit_rows(perms):
    n=len(perms[0]); rows=[]; moments=[]; counts=[]
    for perm in perms:
        assert sorted(perm)==list(range(n))
        seen=set(); mu=[0]*n; cnt=0
        for base in range(n):
            if base in seen: continue
            row=[0]*n; t=base; orb=[]
            while t not in orb:
                orb.append(t); t=perm[t]
            assert t==base and len(orb)==p and not seen.intersection(orb)
            for k,t in enumerate(orb):
                seen.add(t); row[t]=1; mu[t]=k
            rows.append(row); cnt+=1
        moments.append(mu); counts.append(cnt)
    B=nmod_mat(rows,p)
    BM=nmod_mat(rows+moments,p)
    return rows,moments,counts,B.rank(),BM.rank()

single_perms=[[act(x,t) for t in range(q+1)] for x in xs]
single=orbit_rows(single_perms)
points=[(a,b) for a in range(q+1) for b in range(q+1)]
index={x:i for i,x in enumerate(points)}
pairs=[(xs[0],xs[0]),(xs[1],xs[1]),(xs[2],y)]
perms=[[index[(act(m,a),act(n,b))] for a,b in points] for m,n in pairs]
rows,moments,counts,rank,aug=orbit_rows(perms)
def orbits(generators):
    todo=set(range(len(points))); sizes=[]
    while todo:
        seen={min(todo)}; queue=list(seen)
        for x in queue:
            for perm in generators:
                y=perm[x]
                if y not in seen:
                    seen.add(y); queue.append(y)
        todo.difference_update(seen); sizes.append(len(seen))
    return sorted(sizes)
vertex_orbits=[orbits([perms[i],perms[j]]) for i,j in [(0,1),(0,2),(1,2)]]
assert vertex_orbits==[[20,380]]*3
# Solve B lambda=0, mu_i lambda=delta_ij for all three right sides.
equations=rows+moments
augmented=[r+([0,0,0] if i<len(rows) else [int(i-len(rows)==j) for j in range(3)])
           for i,r in enumerate(equations)]
R,rk=nmod_mat(augmented,p).rref()
cycles=[[0]*len(points) for _ in range(3)]
for i in range(rk):
    pivot=next(j for j in range(R.ncols()) if R[i,j])
    assert pivot<len(points)
    for k in range(3): cycles[k][pivot]=int(R[i,len(points)+k])
for k,cycle in enumerate(cycles):
    assert all(sum(a*b for a,b in zip(row,cycle))%p==0 for row in rows)
    assert [sum(a*b for a,b in zip(mu,cycle))%p for mu in moments]==[int(j==k) for j in range(3)]
result={'field':q,'prime':p,'cover_degree':len(points),'edge_orbits':counts,
        'incidence_rank':rank,'augmented_rank':aug,'moment_rank':aug-rank,
        'vertex_orbit_sizes':vertex_orbits,'cycle_nonzero_entries':[sum(x!=0 for x in c) for c in cycles],
        'single_borel_cover':{'degree':20,'incidence_rank':single[3],
                             'augmented_rank':single[4],'moment_rank':single[4]-single[3]}}
base=Path(__file__).parent
(base/'borel_square_moment_result.json').write_text(json.dumps(result,indent=2)+'\n')
(base/'borel_square_matrix.json').write_text(json.dumps({'modulus':p,'rows':rows,'moments':moments})+'\n')
(base/'borel_square_cycles.json').write_text(json.dumps({'modulus':p,'coordinate_order':'(a,b), a then b, 0..18, infinity=19','cycles':cycles},indent=2)+'\n')
print(json.dumps(result))
