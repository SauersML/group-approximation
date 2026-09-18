import json, itertools
reps=json.load(open("q2_presentations.json"))
for k,T in enumerate(reps):
    tf=all(not(a==b==c) for a,b,c in T)
    cols=0
    for s in itertools.product([1,-1],repeat=7):
        if all(not(s[a]==s[b]==s[c]) for a,b,c in T): cols+=1
    print(k,"tf" if tf else "torsion","2-colorings with no monochromatic relator:",cols)
