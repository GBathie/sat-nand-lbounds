"""
This file contains functions that, given a proof annotation `p`, finds the largest `c`
that leads to a contradiction using this proof.
"""
import gurobipy as gp
from gurobipy import GRB

EPS = 0.00000001

def best_param(proof, c_lb=1.0, c_ub=5.0, tol=0.001, verbose=False):
    """
    Find the best possible speedup params so that the annotation `proof`
    leads to a contradiction
    """

    k = len(proof)
    try:
        env = gp.Env(empty=True)
        env.setParam('OutputFlag', 0)
        env.start()
        m = gp.Model(env=env)
        a = m.addVars(k+1, k+1, name='a') # The first row of a is unused except the first var,
                                                  # which represents the runtime of the initial class
        x = m.addVars(k+1, name='x') # params for speedups

        """
        Speedup rule w.p. x:
        (Q_l n^a_l) NDEPTH[a log n] subseteq (Q_l n^max(a_l,x/2)) (Q_{l+1} n^a_l) NDEPTH[(a-x) log n]

        Slowdown Rule:
        (Q_{l-1} n^a_{l-1}) (Q_l n^a_l) NDEPTH[a log n] 
        ((( subseteq (Q_{l-1} n^a_{l-1}) (Q_l n^a_l) TS[n^a]  )))
            subseteq (Q_{l-1} n^a_{l-1}) NDEPTH[c.max(a, a_l, a_{l-1})] 
        """

        # Apply the first speedup
        m.addConstr(a[1, 0] >=  x[1]/2) 
        m.addConstr(a[1, 0] >=  1) 
        # m.addConstr(a[1, 1] >=  x[1]/2)
        m.addConstr(a[1, 1] >=  1)
        m.addConstr(a[1, 2] >=  a[0,0] - x[1])
        l = 1

        # First, build the model without the constraints including `c`
        # Annotation 1 = speedup, 0 = slowdown
        for i in range(1, k):
            r_type = proof[i]
            if r_type == '0': # slowdown
                m.addConstrs(a[i+1, j] == a[i, j] for j in range(l))
                l -= 1
            elif r_type == '1': # speedup
                m.addConstrs(a[i+1, j] == a[i, j] for j in range(l))
                m.addConstr(a[i+1, l] >= a[i, l])
                m.addConstr(a[i+1, l] >= x[i+1]/2)
                m.addConstr(a[i+1, l+1] >= a[i, l])
                # m.addConstr(a[i+1, l+1] >= x[i+1]/2) # WE DO NOT NEED TO BE LARGER THAN X, THIS IS A LOGN QUANTIFIER
                m.addConstr(a[i+1, l+2] == a[i, l+1] - x[i+1])
                l += 1
            else:
                print(f'Incorrect rule type: {r_type}')
                exit(1)

        m.addConstr(a[k,0] <= a[0,0] - EPS)
        # Binary search for best c:
        best = 0
        best_a = 0
        bestp = ''
        while c_ub - c_lb > tol:
            mid = (c_ub + c_lb)/2
            if is_feasible(m, proof, a, mid):
                c_lb = mid
                if mid > best:
                    best = mid
                    best_a = a[0, 0].x
                    bestp = [x[i].x for i in range(0, k+1)]
                    if verbose:
                        pretty_print_sol(proof, a, x, mid)
            else:
                c_ub = mid

        return best, proof, bestp, best_a
    except gp.GurobiError as e:
        print('Error code ' + str(e.errno) + ': ' + str(e))

    except AttributeError:
        print('Encountered an attribute error')


def is_feasible(m, proof, a, c):
    k = len(proof)
    l = 1
    c_constr = []
    # Add the constraints with `c`
    for i in range(1, k):
        r_type = proof[i]
        if r_type == '0': # slowdown
            c_constr.append(m.addConstr(a[i+1, l] >= c*a[i, l+1]))
            c_constr.append(m.addConstr(a[i+1, l] >= c*a[i, l]))
            if l > 0:
                c_constr.append(m.addConstr(a[i+1, l] >= c*a[i, l-1]))
            l -= 1
        elif r_type == '1': # speedup
            l += 1

    m.optimize()
    res = m.status == GRB.OPTIMAL
    m.remove(c_constr)

    return res


def pretty_print_sol(proof, a, x, c):
    k = len(proof)
    print('-----------------------------')
    print(f'Found: SAT is not in Nand-depth[{c} log n]')
    print(f'Annotation: {proof}')
    print()
    print(f'Nand-depth[{a[0,0].x:.5f} log n]')
    l = 1
    print(f'\\subseteq (E n^{a[1,0].x:.5f}) (A n^{a[1,1].x:.5f}) Nand-depth[{a[1,2].x:.5f} log n]  (param {x[1].x:.5f})')
    for i in range(1, k):
        r_type = proof[i]
        if r_type == '0': # slowdown
            l -= 1
        elif r_type == '1': # speedup
            l += 1
        else:
            print(f'Incorrect rule type: {r_type}')
            exit(1)
        s = '\\subseteq ' \
            + ' '.join((f'({"E" if j%2 == 0 else "A"} n^{a[i+1,j].x:.5f})' for j in range(l+1))) \
            + f' Nand-depth[{a[i+1,l+1].x:.5f} log n]'
        print(s + (f'  (param {x[i+1].x:.5f})' if r_type == '1' else ''))
    print('-----------------------------')



def best_param_sparse(proof, c_lb=1.0, c_ub=5.0, tol=0.001, verbose=False):
    """
    Tries to find the best possible `c` between `c_lb` and `c_ub`
    using binary search.
    The generated linear program has 3k+O(1) variables, where k = len(proof).
    """
    k = len(proof)
    try:
        env = gp.Env(empty=True)
        env.setParam('OutputFlag', 0) # disable output
        env.start()
        m = gp.Model(env=env)

        nl = k+1 # number of lines
        # We only keep track of the last two quantifiers: the current class is
        # (Q_l n^a) (Q_{l+1} n^b) NDEPTH[r log n]
        a = m.addVars(nl, name='a') # 2nd-to-last quantifier exponent
        b = m.addVars(nl, name='b') # last quantifier exponent
        r = m.addVars(nl, name='b') # "runtime" 
        x = m.addVars(nl, name='x') # params for speedups

        """
        Speedup rule w.p. x:
        (Q_l n^a_l) NDEPTH[a log n] subseteq (Q_l n^max(a_l,x/2)) (Q_{l+1} n^a_l) NDEPTH[(a-x) log n]

        Slowdown Rule:
        (Q_{l-1} n^a_{l-1}) (Q_l n^a_l) NDEPTH[a log n] 
        ((( subseteq (Q_{l-1} n^a_{l-1}) (Q_l n^a_l) TS[n^a]  )))
            subseteq (Q_{l-1} n^a_{l-1}) NDEPTH[c.max(a, a_l, a_{l-1})] 
        """

        # Apply the first speedup
        m.addConstr(a[1] >=  x[1]/2) 
        m.addConstr(a[1] >=  1) 
        m.addConstr(b[1] >=  1)
        m.addConstr(r[1] >=  r[0] - x[1])
        # l = 1

        stack = [1, 1, a[1], b[1]]
        # i_proof = [2*int(c)-1 for c in proof]
        # ll[i] is the number of quantifiers on line i
        # ll = [0] + [1 + sum(i_proof[:i]) for i in range(1,k+1)]
        # print(ll)
        # First, build the model without the constraints including `c`
        # Annotation 1 = speedup, 0 = slowdown
        set_c = []
        for i in range(2, k+1):
            r_type = proof[i-1]
            if r_type == '0': # slowdown
                m.addConstr(a[i] == stack[-3])
                m.addConstr(b[i] == stack[-2])
                set_c.append(
                    ((stack[-1], stack[-2], r[i], r[i-1]),
                    lambda c, u, v, next_r, old_r: 
                    [ 
                        m.addConstr(next_r >= c*old_r),
                        m.addConstr(next_r >= c*u),
                        m.addConstr(next_r >= c*v)
                                ]
                                ) 
                    )
                stack.pop()
            elif r_type == '1': # speedup
                m.addConstr(a[i] >= stack[-1])
                m.addConstr(a[i] >= x[i]/2)
                m.addConstr(b[i] >= stack[-1])
                m.addConstr(r[i] == r[i-1] - x[i])
                stack.pop()
                stack.append(a[i])
                stack.append(b[i])
            else:
                print(f'Incorrect rule type: {r_type}')
                exit(1)

        m.addConstr(r[k] <= r[0] - EPS)

        def feasible(c):
            c_constr = []
            for par, f in set_c:
                c_constr += f(c, *par)

            m.optimize()
            res = m.status == GRB.OPTIMAL
            m.remove(c_constr)
            return res
        # Binary search for best c:
        best = 0
        best_x = [] # best list of params
        best_r = 0 # best starting running time
        while c_ub - c_lb > tol:
            mid = (c_ub + c_lb)/2
            if feasible(mid):
                c_lb = mid
                if mid > best:
                    best = mid
                    best_x = [x[i].x for i in x]
                    best_r = r[0].x
                    if verbose:
                        print(f'Value {mid} feasible')
                        pretty_print_sparse(proof, mid, x, a, b, r)
            else:
                c_ub = mid
                if verbose:
                    print(f'Value {mid} unfeasible')

        return best, proof, best_x, best_r
    except gp.GurobiError as e:
        print('Error code ' + str(e.errno) + ': ' + str(e))

    except AttributeError:
        print('Encountered an attribute error')

def print_stack(q, r, param=None):
    s = '\\subseteq ' \
        + ' '.join((f'({"E" if i%2 == 0 else "A"} n^{q[i].x:.5f})' for i in range(len(q)))) \
        + f' Nand-depth[{r.x:.5f} log n]'
    if param is not None:
        s += f'   (param {param.x})'
    print(s)

def pretty_print_sparse(p, c, x, a, b, r):
    k = len(p)
    print('-----------------------------')
    print(f'Found: SAT is not in Nand-depth[{c} log n]')
    print(f'Annotation: {p}')
    print()
    print('x:', ' '.join(map(str, (x[i].x for i in x))))
    print('a:', ' '.join(map(str, (a[i].x for i in a))))
    print('b:', ' '.join(map(str, (b[i].x for i in b))))
    print('r:', ' '.join(map(str, (r[i].x for i in r))))
    print()
    print(f'Nand-depth[{r[0].x:.5f} log n]')
    stack = [1]
    # print_stack(stack, r[1], x[1])
    for i in range(1, k+1):
        r_type = p[i-1]
        if r_type == '0': # slowdown
            stack.pop()
            print_stack(stack, r[i])
        elif r_type == '1': # speedup
            stack.pop()
            stack.append(a[i])
            stack.append(b[i])
            print_stack(stack, r[i], x[i])
        else:
            print(f'Incorrect rule type: {r_type}')
            exit(1)
    print('-----------------------------')