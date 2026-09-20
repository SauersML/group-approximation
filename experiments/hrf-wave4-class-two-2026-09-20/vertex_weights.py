"""Exact vertex Lie weights and independent Schreier H1 certificate over F7."""
from pathlib import Path
import json

P=7
def mul(a,b):
    return [[sum(a[i][k]*b[k][j] for k in range(4))%P for j in range(4)] for i in range(4)]
def add(a,b):return [[(x+y)%P for x,y in zip(r,s)] for r,s in zip(a,b)]
def scale(a,n):return [[n*x%P for x in r] for r in a]
def bracket(a,b):return add(mul(a,b),scale(mul(b,a),-1))
def rank(rows):
    rows=[r[:] for r in rows];k=0
    for j in range(len(rows[0])):
        i=next((i for i in range(k,len(rows)) if rows[i][j]%P),None)
        if i is None:continue
        rows[k],rows[i]=rows[i],rows[k];v=pow(rows[k][j]%P,-1,P)
        rows[k]=[x*v%P for x in rows[k]]
        for i in range(len(rows)):
            if i!=k:
                v=rows[i][j];rows[i]=[(x-v*y)%P for x,y in zip(rows[i],rows[k])]
        k+=1
        if k==len(rows):break
    return k

zero=[[0]*4 for _ in range(4)]
la=[r[:] for r in zero];la[0][3]=la[1][2]=1
lb=[r[:] for r in zero];lb[1][0]=1;lb[2][3]=6
lc=[r[:] for r in zero];lc[3][1]=1
out=[]
for name,x,y,expected,sign in [('H0',la,lb,2,0),('H1',lb,lc,3,-1),('H2',lc,la,3,1)]:
    u=add(x,scale(y,-1));v=bracket(x,y);w=bracket(u,v)
    xx=bracket(x,v);yy=bracket(y,v)
    assert rank([sum(u,[]),sum(v,[]),sum(w,[])])==expected
    assert bracket(u,w)==zero and bracket(v,w)==zero
    assert scale(add(xx,yy),-1)==scale(w,sign)
    out.append({'vertex':name,'u':u,'v':v,'w':w,'lie_dimension':expected,
                'cubic_coefficient_sign_over_12':sign,
                'cubic_is_in_vertex_derived':True})

# Free words use signed a=1,b=2,c=3. Schreier transversal 1,a,...,a^6.
def inv(w):return [-s for s in reversed(w)]
def comm(u,v):return inv(u)+inv(v)+u+v
a,b,c=[1],[2],[3]
rels=[b*7,c*7,comm(comm(a,b),a),comm(comm(a,b),b),
      comm(comm(c,b),c),comm(comm(comm(c,b),b),c),comm(comm(comm(c,b),b),b),
      comm(comm(c,a),c),comm(comm(comm(c,a),a),c),comm(comm(comm(c,a),a),a)]
rows=[]
for start in range(7):
    for rel in rels:
        state=start;row=[0]*14
        for s in rel:
            direction=1 if s>0 else -1
            idx=state if s>0 else (state-1)%7
            if abs(s)==2:row[idx]=(row[idx]+direction)%7
            if abs(s)==3:row[7+idx]=(row[7+idx]+direction)%7
            state=(state+direction)%7
        assert state==start
        rows.append(row)
schreier_rank=rank(rows);assert schreier_rank==10
result={'prime':7,'vertex_lie_weights':out,
        'schreier_generators':14,'schreier_abelian_relation_rows':70,
        'schreier_abelian_relation_rank':schreier_rank,
        'K7_H1_F7_dimension':14-schreier_rank}
Path(__file__).with_name('vertex_weights.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='vertex_lie_weights'},indent=2))
