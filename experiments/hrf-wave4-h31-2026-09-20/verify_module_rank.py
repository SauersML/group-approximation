"""Independent sparse mod-five rank verification; standard library only."""
import heapq
import json
import time
from pathlib import Path

base=Path(__file__).parent
data=json.loads((base/'retraction_module_rows.json').read_text())
p=data['modulus']; n=data['cols']; assert p==5 and n==2976
rows=[{int(k):v for k,v in row.items()} for row in data['rows']]
assert len(rows)==14880
assert all(all(0<=j<n and 0<v<p for j,v in row.items()) and sum(row.values())%p==0 for row in rows)
columns=[set() for _ in range(n)]
heap=[]
for i,row in enumerate(rows):
    for j in row: columns[j].add(i)
    if row: heapq.heappush(heap,(len(row),i))
pivots=[]; initial=time.monotonic()
while heap:
    length,i=heapq.heappop(heap)
    row=rows[i]
    if not row or len(row)!=length:continue
    j=min(row,key=lambda j:(len(columns[j]),j))
    coeff=row[j]; inv=pow(coeff,-1,p)
    normalized={k:v*inv%p for k,v in row.items()}
    targets=list(columns[j]-{i})
    for k in row: columns[k].remove(i)
    rows[i]={}
    for target in targets:
        other=rows[target]; factor=other[j]
        for k,v in normalized.items():
            old=other.get(k,0);new=(old-factor*v)%p
            if new:
                other[k]=new
                if not old:columns[k].add(target)
            elif old:
                del other[k];columns[k].remove(target)
        if other:heapq.heappush(heap,(len(other),target))
    assert not columns[j]
    pivots.append((i,j,coeff))
    if len(pivots)%500==0:print('pivots',len(pivots),'seconds',round(time.monotonic()-initial,3),flush=True)
assert not any(rows) and len({x[1] for x in pivots})==len(pivots)
assert len(pivots)==2975
out={'modulus':p,'rank':len(pivots),'nullity':n-len(pivots),'all_rows_eliminated':True,
     'method':'Sparse exact elimination with minimum support pivot rows and column degrees',
     'elapsed_seconds':time.monotonic()-initial,'pivots':pivots}
(base/'retraction_module_rank_certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS:2975independentpivots;nullity1;all14880rowseliminated',flush=True)
