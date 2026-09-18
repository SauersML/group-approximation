import json
from lo_sat_sub import run_sub
reps=json.load(open("q2_presentations.json")); Q=json.load(open("quotients7.json"))
for k,m in [("4",3),("4",5),("4",6),("4",7),("7",1),("8",0),("8",2)]:
    print(k,m,run_sub(7,reps[int(k)],Q[k][m],4),flush=True)
