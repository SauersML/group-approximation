pkill -u sauer354 -f "optimize6.py pres6.json 3 seed:" || true
pkill -u sauer354 -f "optimize6.py pres6.json 3 random 6" || true
sleep 1; ps -u sauer354 -o cmd | grep "^python3 optimize6" | cut -c1-90
