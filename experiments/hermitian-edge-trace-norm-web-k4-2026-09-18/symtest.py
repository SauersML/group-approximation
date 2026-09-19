# Numerical sanity check of the symmetry domain D used by k5a/k5b (the proof is the orbit argument in README.md):
# every admissible C on K5 has an image under S5 x conj x neg whose star-gauged phases lie in D
import numpy as np, itertools, math
rng=np.random.default_rng(1)
def u(t): r=t%math.pi; return min(r,math.pi-r)
free=[(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
def gauged(C):
    """diagonal unitary gauge making C_0i real positive; returns the six free phases and the gauged matrix"""
    d=np.array([1]+[np.conj(C[0,i])/abs(C[0,i]) for i in range(1,5)])
    Cg=np.diag(np.conj(d))@C@np.diag(d)
    assert all(abs(Cg[0,i].imag)<1e-9 and Cg[0,i].real>0 for i in range(1,5))
    return {e:np.angle(Cg[e])%(2*math.pi) for e in free}, Cg
def inD(th):
    if not (0<=th[(1,2)]<=math.pi/2): return False
    U=lambda *ts: u(sum(s*th[e] for e,s in ts))
    tri=[U(((1,2),1),((2,3),1),((1,3),-1)),U(((1,2),1),((2,4),1),((1,4),-1)),U(((1,3),1),((3,4),1),((1,4),-1)),U(((2,3),1),((3,4),1),((2,4),-1))]
    a=u(th[(1,2)])
    if any(u(th[e])<a for e in free[1:]) or any(t<a for t in tri): return False
    b=u(th[(1,3)])
    if any(x<b for x in [u(th[(2,3)]),tri[0],u(th[(1,4)]),u(th[(2,4)]),tri[1]]): return False
    return True
bad=0; N=3000
for s in range(N):
    C=np.zeros((5,5),complex)
    for i in range(5):
        for j in range(i+1,5): C[i,j]=rng.uniform(1,2)*np.exp(1j*rng.uniform(0,2*math.pi)); C[j,i]=np.conj(C[i,j])
    n0=np.abs(np.linalg.eigvalsh(C)).sum(); ok=False
    for p in itertools.permutations(range(5)):
        P=np.eye(5)[list(p)]
        for cj in (0,1):
            for ng in (1,-1):
                C2=ng*(P@C@P.T); C2=np.conj(C2) if cj else C2
                th,Cg=gauged(C2)
                if inD(th):
                    ok=True; assert abs(np.abs(np.linalg.eigvalsh(Cg)).sum()-n0)<1e-9; break
            if ok: break
        if ok: break
    bad+= not ok
print("samples",N,"without image in D:",bad)
