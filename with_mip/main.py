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
            x = params[i+1]
            r = c*max(r-x, x, q[-1], q[-2]) if len(q) > 1 else c*max(r-x, x, q[-1])
            q.pop()
            print_anno(q, r, None)
        elif annotation[i] == '2':
            r = c*max(r, q[-1], q[-2]) if len(q) > 1 else c*max(r, q[-1])
            q.pop()
            print_anno(q, r)
        else:
            print('Incorrect annotation')
            exit(0)
    print('Correct proof!' if r < p0 else 'Incorrect proof :(')


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
    if k == 0:
        return '0'
    return '1' + good_annotation(k-1) + '10'*k + '0'

def try_good_proof():
    for s in [3,5,10,15,30,50]:
        t = time()
        c,p,x,r = best_param_sparse(good_annotation(s))
        t2 = time()
        print(f'Best c found: {c:.5f} in {(t2-t):.5f}s for annotation {p}')


def try_proof(p):
    t = time()
    c,p,x,r = best_param_sparse(p, verbose=1)
    t2 = time()
    print(f'Best c found: {c:.5f} in {(t2-t):.5f}s for annotation {p}')


if __name__ == '__main__':
    # try_good_proof()
    # try_proof('11010100100')
    # exit(0)
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
