"""
Use MIP models to:
- find optimal parameters for fixed proof annotations
- search optimal proof annotations 
"""
import argparse

from pyparams import best_param, best_param_sparse
from pysearch import best_proof, best_proof_sparse

def dyck(n):
    if n == 0:
        yield ''
        return
    for i in range(1,n+1): # choose a number of 'up' steps before reaching 0 for the 1st time
        for p1 in dyck(i-1):
            for p2 in dyck(n-i):
                yield '1'+p1+'0'+p2

def enumerate_annotations(n):
    for p in dyck(n):
        yield p + '0'

def print_anno(q, r, x=None):
    s = '\\subseteq ' \
        + ' '.join(f'({"E" if i%2 == 0 else "A"} n^{q[i]:.5f})' for i in range(len(q))) \
        + f' Nand-depth[{r} log n]'
    if x is not None:
        s += f'   (param {x:.5f})'
    print(s)

def run_proof(annotation, params, p0, c):
    k = len(annotation)
    print('----------------')
    print(f'Running proof for {c} with annotation {annotation}')
    print(f'Parameters: {params}')
    print()
    print(f'Nand-depth[{p0} log n]')
    x = params[1]
    q = [x/2, 1]
    r = p0 - x
    print_anno(q, r, x)
    for i in range(1, k):
        if annotation[i] == '1':
            x = params[i+1]
            q.append(q[-1])
            q[-2] = max(q[-2], x/2)
            r = r - x
            print_anno(q, r, x)
        elif annotation[i] == '0':
            r = c*max(r, q[-1], q[-2]) if len(q) > 1 else c*max(r, q[-1])
            q.pop()
            print_anno(q, r)
        else:
            print('Incorrect annotation')
            exit(0)


from time import time

def time_generated_search(size, f, print_proof=False, **kwargs):
    t = time()
    best_c, best_proof, best_x, best_r = 0, '', [], 0
    for p in enumerate_annotations(size):
        c, proof, x, r = f(p, **kwargs)
        if c > best_c:
            best_c, best_proof, best_x, best_r = c, proof, x, r
    t2 = time()
    print(f'Best c found: {best_c:.5f} in {(t2-t):.5f}s for annotation {best_proof}')
    if print_proof:
        run_proof(best_proof, best_x, best_r, best_c)
    

def time_search(size, f, print_proof=False, **kwargs):
    t = time()
    best_c, best_proof, best_x, best_r = f(size, **kwargs)
    t2 = time()
    print(f'Best c found: {best_c:.5f} in {(t2-t):.5f}s for annotation {best_proof}')
    if print_proof:
        run_proof(best_proof, best_x, best_r, best_c)

def good_annotation(k):
    return '1'*(k-1) + '100'*k

def time_functions(s, debug=False):
    time_search(s, best_proof, debug)
    time_generated_search(s, best_param_sparse, debug)
    time_generated_search(s, best_param, debug)

def try_good_proof():
    for s in [10,20,30,40,50]:
        t = time()
        c,p,x,r = best_param(good_annotation(s))
        t2 = time()
        print(f'Best c found: {c:.5f} in {(t2-t):.5f}s for annotation {p}')

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("depth", help="Number of 'up' steps in target proofs", type=int)
    parser.add_argument('-v', '--verbose', help="Activate debug of search functions", action='store_true')
    parser.add_argument('-e', '--enumerate', help="Enumerate proofs instead of using MIP", action='store_true')
    args = parser.parse_args()

    if args.enumerate:
        time_generated_search(args.depth, best_param_sparse, print_proof=args.verbose, verbose=args.verbose)
    else:
        # time_search(args.depth, best_proof, print_proof=args.verbose, verbose=args.verbose, c_lb=2, c_ub=3)
        time_search(args.depth, best_proof_sparse, print_proof=args.verbose, n_threads=31, verbose=args.verbose, c_lb=2, c_ub=3)
