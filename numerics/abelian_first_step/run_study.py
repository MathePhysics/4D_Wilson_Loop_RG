"""Run the abelian first-step study and write results/*.json.  Usage: python3 run_study.py D L K n1,n2,..."""
import json, os, sys, time
import abelian_first_step as af

d, L, K = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
ns = tuple(int(x) for x in sys.argv[4].split(','))
t = time.time()
gauges = tuple(sys.argv[5].split(',')) if len(sys.argv) > 5 else ('landau', 'xi1', 'total')
r = af.loop_energies(d, L, K, ns, gauges=gauges)
os.makedirs('results', exist_ok=True)
out = {'d': d, 'L': L, 'K': K, 'n': list(ns), 'seconds': time.time() - t,
       'E': {f'{g}:{n}': v for (g, n), v in r.items()}}
json.dump(out, open(f'results/d{d}_L{L}_K{K}_n{"-".join(map(str,ns))}.json', 'w'), indent=1)
print(json.dumps(out, indent=1))
