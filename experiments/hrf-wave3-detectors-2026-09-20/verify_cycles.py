"""Check the three obstruction cycles using only standard-library integer arithmetic."""
import json
from pathlib import Path

q=19; p=5
xs=[(2,11,16,3),(5,11,4,9),(6,15,12,8)]
pairs=[(xs[0],xs[0]),(xs[1],xs[1]),(xs[2],(1,8,12,6))]
def act(m,t):
    a,b,c,d=m
    if t==19:
        return a*pow(c,-1,19)%19 if c else 19
    den=(c*t+d)%19
    return (a*t+b)*pow(den,-1,19)%19 if den else 19

points=[(a,b) for a in range(20) for b in range(20)]
index={x:i for i,x in enumerate(points)}
cycles=json.loads(Path(__file__).with_name('borel_square_cycles.json').read_text())['cycles']
assert len(cycles)==3 and all(len(c)==400 and all(0<=x<5 for x in c) for c in cycles)
all_moments=[]
for pair in pairs:
    perm=[index[(act(pair[0],a),act(pair[1],b))] for a,b in points]
    assert sorted(perm)==list(range(400))
    seen=set(); values=[0,0,0]; count=0
    for base in range(400):
        if base in seen: continue
        orbit=[]; x=base
        while x not in orbit:
            orbit.append(x); x=perm[x]
        assert x==base and len(orbit)==5 and not seen.intersection(orbit)
        seen.update(orbit); count+=1
        for i,cycle in enumerate(cycles):
            assert sum(cycle[x] for x in orbit)%5==0
            values[i]=(values[i]+sum(k*cycle[x] for k,x in enumerate(orbit)))%5
    assert count==80
    all_moments.append(values)
assert all_moments==[[1,0,0],[0,1,0],[0,0,1]]
print('PASS: all240 orbit sums vanish; the3 by3 moment matrix is identity modulo5.')
