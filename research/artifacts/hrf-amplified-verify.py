"""Standard-library, input-bound associator certificate verifier; MSI only."""
from pathlib import Path
import itertools, json, sys, time

started=time.monotonic()
path=Path(sys.argv[1] if len(sys.argv)>1 else '/projects/standard/hsiehph/sauer354/hrf-amplified-2026-09-20/certificates.json')
bundle=json.loads(path.read_text())
# Encode a+b*z as a+19*b, with z^2=4*z-1. Tables only accelerate exact arithmetic.
ADD=[[((x%19+y%19)%19)+19*((x//19+y//19)%19) for y in range(361)] for x in range(361)]
MUL=[[((x%19*(y%19)-x//19*(y//19))%19)+19*((x%19*(y//19)+x//19*(y%19)+4*(x//19)*(y//19))%19) for y in range(361)] for x in range(361)]
NEG=[((-x%19)%19)+19*((-(x//19))%19) for x in range(361)]
def power(x,n):
    answer=1
    while n:
        if n&1: answer=MUL[answer][x]
        x=MUL[x][x]; n//=2
    return answer
def eye(n): return [[int(i==j) for j in range(n)] for i in range(n)]
def mm(X,Y):
    n=len(Y[0]); result=[[0]*n for _ in X]
    for i,row in enumerate(X):
      for h,x in enumerate(row):
       if x:
        mr=MUL[x]
        for j,y in enumerate(Y[h]):
         if y: result[i][j]=ADD[result[i][j]][mr[y]]
    return result
def plus(X,Y): return [[ADD[x][y] for x,y in zip(a,b)] for a,b in zip(X,Y)]
def negative(X): return [[NEG[x] for x in row] for row in X]
def cols(X,indices): return [[row[j] for j in indices] for row in X]
def inverse(X):
    n=len(X); assert all(len(row)==n for row in X)
    rows=[list(row)+unit for row,unit in zip(X,eye(n))]
    for c in range(n):
        p=next((i for i in range(c,n) if rows[i][c]),None)
        assert p is not None,'singular certificate matrix'
        rows[c],rows[p]=rows[p],rows[c]
        r=power(rows[c][c],359); assert MUL[r][rows[c][c]]==1
        rows[c]=[MUL[r][x] for x in rows[c]]
        for i in range(n):
            if i!=c and rows[i][c]:
                factor=rows[i][c]
                rows[i]=[ADD[x][NEG[MUL[factor][y]]] for x,y in zip(rows[i],rows[c])]
    answer=[row[n:] for row in rows]
    assert mm(X,answer)==eye(n)
    return answer
def check(X,r,c):
    assert len(X)==r and all(len(row)==c for row in X)
    assert all(type(x) is int and 0<=x<361 for row in X for x in row)
    return X
def decode(X):
    return [[sum(c*19**i for i,c in enumerate(x)) for x in row] for row in X]
def sym4(g):
    a,b,c,d=g; assert (a*d-b*c)%19==1
    columns=[]
    for i in range(5):
        p=[1]
        for s,t in [(a,c)]*(4-i)+[(b,d)]*i:
            q=[0]*(len(p)+1)
            for j,v in enumerate(p):
                q[j]=(q[j]+s*v)%19; q[j+1]=(q[j+1]+t*v)%19
            p=q
        columns.append(p)
    return [[columns[j][i] for j in range(5)] for i in range(5)]

assert all((x*x-4*x+1)%19 for x in range(19))
assert power(19,5)==1 and 19!=1
metadata=bundle['input']
assert metadata['characteristic']==19 and metadata['modulus']=='z^2-4*z+1'
A,B,C=[sym4(g) for g in [(2,11,16,3),(5,11,4,9),(6,15,12,8)]]
for name,X in zip(['A','B','C'],[A,B,C]):
    assert decode(metadata[name])==X
    Y=eye(5)
    for _ in range(5): Y=mm(Y,X)
    assert Y==eye(5)
roots=[power(19,j) for j in range(5)]
D=[[roots[i] if i==j else 0 for j in range(5)] for i in range(5)]
bases=[]
for name,X in [('PB',B),('PC',C)]:
    P=check(decode(metadata[name]),5,5); Pi=inverse(P)
    assert mm(X,P)==mm(P,D)
    bases.append((P,Pi))
def pieces(P,Pi,s):
    return [[[MUL[P[i][(h-s)%5]][Pi[h][j]] for j in range(5)] for i in range(5)] for h in range(5)]
V=[pieces(*bases[0],b) for b in range(5)]
W=[pieces(*bases[1],c) for c in range(5)]
products={(b,c):[mm(V[b][i],W[c][j]) for i in range(5) for j in range(5)] for b in range(5) for c in range(5)}
cases=bundle['cases']; triples=[tuple(case['triple']) for case in cases]
assert len(triples)==124 and set(triples)==set(itertools.product(range(5),repeat=3))-{(0,0,0)}
boundary=[0,1,2,3,4,5,10,15,20]
interior=[5*i+j for i in range(1,5) for j in range(1,5)]
unit=[1,0,0,0,0]
for case in cases:
    a,b,c=case['triple']
    L=[[0]*25 for _ in range(25)]
    for h,X in enumerate(products[b,c]):
        XA=mm(X,A); AX=mm(A,X)
        for i in range(5):
          for j in range(5): L[5*i+j][h]=ADD[XA[i][j]][NEG[MUL[roots[a]][AX[i][j]]]]
    H=check(case['H'],4,25)
    assert mm(H,cols(L,interior))==[[0]*16 for _ in range(4)]
    LR=mm(H,cols(L,boundary))
    free=case['free']; assert len(free)==4 and len(set(free))==4 and all(0<=i<8 for i in free)
    piv=[i for i in range(8) if i not in free]
    inverse(cols(LR,[i+1 for i in piv]))
    coeff=check(case['coeff'],8,5)
    for j,i in enumerate(free): assert coeff[i]==eye(5)[j+1]
    assert mm(LR,[unit]+coeff)==[[0]*5 for _ in range(4)]
    ww=[unit]+coeff[:4]; vv=[unit]+coeff[4:]
    T=[[0]*21 for _ in range(25)]
    for i in range(5):
      for j in range(5):
       for u in range(5):
        for v in range(5):
         col=0 if u==v==0 else (max(u,v) if u==0 or v==0 else 5+4*(u-1)+v-1)
         T[5*i+j][col]=ADD[T[5*i+j][col]][MUL[vv[i][u]][ww[j][v]]]
    Q=mm(L,T); Qlow=cols(Q,range(5)); Qquad=cols(Q,range(5,21))
    qr=case['quadratic_rows']; assert len(qr)==16 and len(set(qr))==16 and all(0<=i<25 for i in qr)
    inverse([Qquad[i] for i in qr])
    table=check(case['table'],16,5)
    assert plus(mm(Qquad,table),Qlow)==[[0]*5 for _ in range(25)]
    basis=eye(5)
    def product(x,y):
        result=[0]*5
        for i in range(5):
          for j in range(5):
            value=MUL[x[i]][y[j]]
            if not value: continue
            row=basis[max(i,j)] if i==0 or j==0 else table[4*(i-1)+j-1]
            for h,q in enumerate(row): result[h]=ADD[result[h]][MUL[value][q]]
        return result
    assoc=[]
    for i,j,h in itertools.product(range(1,5),repeat=3):
        left=product(product(basis[i],basis[j]),basis[h])
        right=product(basis[i],product(basis[j],basis[h]))
        assoc.append([ADD[x][NEG[y]] for x,y in zip(left,right)])
    ai=case['associator_indices']; assert len(ai)==5 and all(0<=i<64 for i in ai)
    witness=check([case['unit_witness']],1,5)
    assert mm(witness,[assoc[i] for i in ai])==[unit]
print('PASS',json.dumps({'triples':124,'pinned_sym4_inputs_and_eigenbases':True,
    'linear_elimination_witnesses_bound_to_edge_equations':True,
    'quadratic_tables_bound_to_all_substituted_equations':True,
    'associator_unit_identities':124,'scope':'all multiplicities over all characteristic-19 extension fields',
    'seconds':time.monotonic()-started}))
