"""MSI-only exact linear probe; no noncommutative products are commuted."""
from sage.all import GF, PolynomialRing, matrix, diagonal_matrix, identity_matrix
from pathlib import Path
import json, itertools, time

started=time.monotonic()
out=Path('/projects/standard/hsiehph/sauer354/hrf-amplified-2026-09-20')
data=json.loads(Path('/projects/standard/hsiehph/sauer354/hrf-breakthrough-2026-09-20-sym4/input.json').read_text())
F=GF(19); P=PolynomialRing(F,'t'); t=P.gen()
k=GF(361,name='z',modulus=t*t-4*t+1); z=k.gen()
def decode(X):
    return matrix(k,[[sum(k(c)*z**i for i,c in enumerate(e)) for e in row] for row in X])
A,B,C,PB,PC=[decode(data[n]) for n in ['A','B','C','PB','PC']]
def pieces(P,e):
    T=matrix(k,5,5,lambda i,j:int(i==(j-e)%5))
    return [P*T*diagonal_matrix(k,[int(i==j) for i in range(5)])*P.inverse() for j in range(5)]
records=[]
certificates=[]
def enc(M):
    return [[int(x.polynomial()[0])+19*int(x.polynomial()[1]) for x in row] for row in M]
for a,b,c in itertools.product(range(5),repeat=3):
    if not any((a,b,c)): continue
    V=pieces(PB,b); W=pieces(PC,c)
    L=matrix(k,[(V[i]*W[j]*A-z**a*A*V[i]*W[j]).list() for i in range(5) for j in range(5)]).transpose()
    boundary=[0]+list(range(1,5))+[5*i for i in range(1,5)]
    interior=[5*i+j for i in range(1,5) for j in range(1,5)]
    H=L.matrix_from_columns(interior).left_kernel().basis_matrix()
    LR=H*L.matrix_from_columns(boundary)
    chosen=list(LR.transpose().pivots())
    H=H.matrix_from_rows(chosen); LR=LR.matrix_from_rows(chosen)
    rec={'triple':[a,b,c],'product_rank':L.rank(),'interior_rank':L.matrix_from_columns(interior).rank(),'linear_rank':LR.rank()}
    # Linear normalized relations, column order 1,w1..w4,v1..v4.
    # Solve pivots in the eight nonconstant unknowns, retaining formal free ones.
    R=LR.matrix_from_columns(list(range(1,9))+[0]).echelon_form()
    piv=list(R.pivots()); assert 8 not in piv
    free=[i for i in range(8) if i not in piv]
    d=len(free); coeff=[None]*8
    for j,i in enumerate(free): coeff[i]=[k(0)]*(d+1); coeff[i][j+1]=k(1)
    for ri,p in enumerate(piv):
        coeff[p]=[-R[ri,8]]+[-R[ri,j] for j in free]
    one=[k(1)]+[k(0)]*d
    ww=[one]+coeff[:4]; vv=[one]+coeff[4:]
    # Words: empty, each generator, each ordered pair.
    words=[()]+[(i,) for i in range(d)]+list(itertools.product(range(d),repeat=2))
    wi={w:i for i,w in enumerate(words)}
    T=matrix(k,25,len(words))
    for i in range(5):
      for j in range(5):
       for u in range(d+1):
        for v in range(d+1):
         word=(() if u==0 else (u-1,))+(() if v==0 else (v-1,))
         T[5*i+j,wi[word]]+=vv[i][u]*ww[j][v]
    Q=L*T
    comm=matrix(k, [ [int(w==(i,j))-int(w==(j,i)) for w in words] for i in range(d) for j in range(i+1,d)])
    rec.update({'free_generators':d,'relation_rank_degree2':Q.rank(),'commutators_implied':Q.stack(comm).rank()==Q.rank(),'quadratic_rank':Q.matrix_from_columns(list(range(1+d,len(words)))).rank()})
    # Full quadratic rank rewrites every generator product as an affine word.
    table=Q.matrix_from_columns(list(range(1+d,len(words)))).solve_right(-Q.matrix_from_columns(list(range(1+d))))
    assert Q.matrix_from_columns(list(range(1+d,len(words))))*table == -Q.matrix_from_columns(list(range(1+d)))
    from sage.all import vector
    basis=[vector(k,[int(i==j) for i in range(d+1)]) for j in range(d+1)]
    def mul(x,y):
      answer=x[0]*y+y[0]*x-x[0]*y[0]*basis[0]
      for i in range(d):
       for j in range(d): answer+=x[i+1]*y[j+1]*table[d*i+j]
      return answer
    assoc=matrix(k,[mul(mul(x,y),q)-mul(x,mul(y,q)) for x in basis[1:] for y in basis[1:] for q in basis[1:]])
    ideal=assoc.row_space()
    dims=[int(ideal.dimension())]
    while True:
      more=matrix(k,list(ideal.basis())+[mul(x,y) for x in ideal.basis() for y in basis]+[mul(y,x) for x in ideal.basis() for y in basis]).row_space()
      if more==ideal: break
      ideal=more; dims.append(int(ideal.dimension()))
    rec.update({'associator_ideal_dimensions':dims,'algebra_dimension':int(d+1-ideal.dimension()),'unit_killed':bool(basis[0] in ideal)})
    assert d==4 and rec['quadratic_rank']==16 and assoc.rank()==5
    assoc_indices=list(assoc.transpose().pivots())
    assoc_square=assoc.matrix_from_rows(assoc_indices)
    unit_witness=assoc_square.transpose().solve_right(basis[0])
    assert unit_witness*assoc_square==basis[0]
    certificates.append({'triple':[a,b,c],'H':enc(H),'free':free,'coeff':enc(matrix(k,coeff)),
       'quadratic_rows':list(Q.matrix_from_columns(list(range(5,21))).transpose().pivots()),
       'table':enc(table),'associator_indices':assoc_indices,'unit_witness':enc(matrix(k,[unit_witness]))[0]})
    records.append(rec); print(json.dumps(rec),flush=True)
(out/'linear-results.json').write_text(json.dumps(records,indent=2)+'\n')
(out/'certificates.json').write_text(json.dumps({'input':data,'cases':certificates},separators=(',',':'))+'\n')
print('SECONDS',time.monotonic()-started,flush=True)
