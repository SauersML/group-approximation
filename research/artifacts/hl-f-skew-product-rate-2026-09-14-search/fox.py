# Fox winding functions of commutator-subgroup words of F_2 = <a,b> in Z[s^+-1,t^+-1].
# A word is a string over a,b,A,B (capitals = inverses), read left to right as the group product.
from collections import defaultdict
def ab(ch):
    return {'a':(1,0),'A':(-1,0),'b':(0,1),'B':(0,-1)}[ch]
def add(p,q,c=1):
    r=defaultdict(int,p)
    for k,v in q.items(): r[k]+=c*v
    return {k:v for k,v in r.items() if v}
def mul(p,q):
    r=defaultdict(int)
    for (i,j),v in p.items():
        for (k,l),w in q.items(): r[(i+k,j+l)]+=v*w
    return {k:v for k,v in r.items() if v}
def fox(word,x):
    # d w / d x, mapped to Z[Z^2]
    res=defaultdict(int); pre=(0,0)
    for ch in word:
        if ch==x: res[pre]+=1
        e=ab(ch); nxt=(pre[0]+e[0],pre[1]+e[1])
        if ch==x.upper(): res[nxt]-=1
        pre=nxt
    assert pre==(0,0), 'not in commutator subgroup'
    return {k:v for k,v in res.items() if v}
def divide_by_t_minus_1(p):
    # exact division of a Laurent polynomial by (t - 1), column by column in the t-direction
    cols=defaultdict(dict)
    for (i,j),v in p.items(): cols[i][j]=v
    q={}
    for i,col in cols.items():
        js=sorted(col); lo,hi=js[0],js[-1]
        # p_i(t) = q_i(t)(t-1): q_i coefficients from the top down
        coeff={j:col.get(j,0) for j in range(lo,hi+1)}
        qi={}
        carry=0
        for j in range(hi,lo,-1):
            carry = coeff[j] + (qi.get(j,0))
            qi[j-1]=carry
        # check
        prod=defaultdict(int)
        for j,v in qi.items(): prod[j+1]+=v; prod[j]-=v
        prod={k:v for k,v in prod.items() if v}
        want={k:v for k,v in coeff.items() if v}
        assert prod==want, ('not divisible', i, want, prod)
        for j,v in qi.items():
            if v: q[(i,j)]=v
    return q
def W(word):
    return divide_by_t_minus_1(fox(word,'a'))
def show(p):
    return ' + '.join(f"{v}*s^{i}t^{j}" for (i,j),v in sorted(p.items()))
R1='bAABaaBAba'; R2='bAAABaaaBAAbaa'; C='abAB'
for name,w in [('R1',R1),('R2',R2),('C',C)]:
    Wa=W(w); Wb_check=fox(w,'b')
    # consistency: fox_b = -W*(s-1)
    sm1={(1,0):1,(0,0):-1}
    assert Wb_check==add({},mul(Wa,sm1),-1), ('b-derivative mismatch',name)
    print(name, 'W =', show(Wa), '| l1 =', sum(abs(v) for v in Wa.values()))
