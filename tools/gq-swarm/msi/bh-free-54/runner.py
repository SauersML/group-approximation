import threading, sys, runpy
sys.setrecursionlimit(200000)
threading.stack_size(1 << 28)
sys.argv = ["rev.py"] + sys.argv[1:]
t = threading.Thread(target=lambda: runpy.run_path("rev.py", run_name="__main__"))
t.start(); t.join()
