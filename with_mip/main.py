"""
Use MIP models to:
- find optimal parameters for fixed proof annotations
- search optimal proof annotations 
"""
import argparse

from pyparams import best_param_sparse
from pysearch import best_proof_sparse

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
        + ' '.join(f'({"E" if i%2 == 0 else "A"} n^{q[i]:.3f})' for i in range(len(q))) \
        + f' Nand-depth[{r:.3f} log n]'
    if x is not None:
        s += f'   (param {x:.3f})'
    print(s)

def run_proof(annotation, params, p0, c):
    k = len(annotation)
    print('----------------')
    print(f'Running proof for {c} with annotation {annotation}')
    print(f'Parameters: {params}')
    print()
    print(f'Nand-depth[{p0} log n]')
    x = params[1]
    q = [max(x/2, 1), 1]
    r = p0 - x
    print_anno(q, r, x)
    for i in range(1, k):
        if annotation[i] == '1':
            x = params[i+1]
            q.append(1)
            q[-2] = max(q[-2], x/2)
            r = r - x
            print_anno(q, r, x)
        elif annotation[i] == '0':
            r = c*max(r/2, q[-1], q[-2], 1) if len(q) > 1 else c*max(r/2, q[-1], 1)
            q.pop()
            print_anno(q, r, None)
        else:
            print('Incorrect annotation')
            exit(0)
    # Sanity check
    print('Correct proof!' if r < p0 else 'Incorrect proof :(')


from time import time

def time_generated_search(size, f, print_proof=False, **kwargs):
    t = time()
    best_c, best_proof, best_x, best_r = 0, [], [], 0
    for p in enumerate_annotations(size):
        c, proof, x, r = f(p, **kwargs)
        if c > best_c:
            best_c, best_proof, best_x, best_r = c, [proof], x, r
        elif c == best_c:
            best_proof.append(proof)
            print(c, best_proof)
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

if __name__ == '__main__':

    parser = argparse.ArgumentParser()
    parser.add_argument("depth", help="Number of 'up' steps in target proofs", type=int)
    parser.add_argument('-v', '--verbose', help="Activate debug of search functions", action='count', default=0)
    parser.add_argument('-e', '--enumerate', help="Enumerate proofs instead of using MIP", action='store_true')
    parser.add_argument('-t', '--threads', help="Number of threads to use", type=int, default=10)
    args = parser.parse_args()

    if args.enumerate:
        time_generated_search(args.depth, best_param_sparse, print_proof=args.verbose > 0, verbose=args.verbose)
    else:
        time_search(args.depth, best_proof_sparse, print_proof=args.verbose > 0, n_threads=args.threads, verbose=args.verbose, c_lb=2, c_ub=4)
