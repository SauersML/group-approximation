e0,e1,e2 = (1,0,0),(0,1,0),(0,0,1)
v01,v02,u,c = (1,1,0),(1,0,1),(2,0,1),(1,1,1)
def resolve(cell, word):
    """Minimal resolution of a unit-corner line in cell (a0,a1,a2): s splits (a0,a1), t splits (a1,a2);
    keep the child containing the corner at a1, return siblings plus the final corner."""
    a0,a1,a2 = cell; out = []
    for ch in word:
        if ch == 's': out.append((a0, add(a0,a1), a2)); a0 = add(a0,a1)
        else:         out.append((a0, add(a1,a2), a2)); a2 = add(a1,a2)
    return out + [(a0,a1,a2)]
def words(ns, nt):
    from itertools import permutations
    return sorted(set(''.join(p) for p in permutations('s'*ns + 't'*nt)))
ell = lambda v: v[0]-v[1]
H1, H2 = (e0,v01,e2), (v01,e1,e2)
def one_round(cell, pieces):
    """Try each first split of cell: every straddling piece must be cut by the plane through one of its
    own first splits; split those pieces once and test the split-tree property."""
    res = []
    for i,j in [(0,1),(0,2),(1,2)]:
        k = 3-i-j; n = cross(add(cell[i],cell[j]), cell[k]); new = []; ok = True
        for P in pieces:
            vals = [dot(n,v) for v in P]
            if min(vals) >= 0 or max(vals) <= 0: new.append(P); continue
            hit = None
            for a,b in [(0,1),(0,2),(1,2)]:
                cc = 3-a-b; mid = add(P[a],P[b])
                if dot(n,mid) == 0 and dot(n,P[cc]) == 0: hit = (a,b)
            if hit is None: ok = False; break
            a,b = hit; mid = add(P[a],P[b]); A = list(P); A[b] = mid; B = list(P); B[a] = mid
            new += [tuple(A), tuple(B)]
        if ok: res.append(((cell[i],cell[j]), split_tree(cell, new), len(new)))
        else: res.append(((cell[i],cell[j]), 'straddler not cut through its own first split', None))
    return res
for wa in words(1,2):
    for wb in words(2,1):
        Dd = resolve((e0,e1,u), wa) + resolve((u,e1,v02), wb) + [(v02,c,e2),(c,e1,e2)]
        assert sum(weight(P) for P in Dd) == 1 and split_tree((e0,e1,e2), Dd)
        S1 = [P for P in Dd if min(map(ell,P)) >= 0]; S2 = [P for P in Dd if max(map(ell,P)) <= 0]
        assert len(S1)+len(S2) == len(Dd)
        t1, t2 = split_tree(H1,S1), split_tree(H2,S2)
        line = f'{wa} {wb}: H1 tree {t1}, H2 tree {t2}'
        if not t1: line += ' | one round: ' + '; '.join(f'{e}->{r}' for e,r,_ in one_round(H1,S1))
        print(line)
