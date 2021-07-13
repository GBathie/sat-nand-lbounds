from math import *
from fractions import Fraction

# Apply the speedup lemma once
# with an E or A as first quantifier
# and with parameter x:
# NAND-depth[c log n] \subseteq (E n^{x/2}) (A x/2 log n) NAND-depth[(c-x) log n]
def speedup(cc, x, E=True):
	ccr = cc[:-1]
	nd = cc[-1]
	assert nd['type'] == 'nand', f"Cannot apply the speedup lemma to a non-NAND-depth class {nd}"
	first_q = 'E' if E else 'A'
	sec_q = 'A' if E else 'E'
	c1 = {'type':first_q, 'const':x*nd['const']/2, 'func':'poly'}
	if len(ccr) > 0:
		lq = ccr[-1]
		if lq['type'] == first_q:
			if lq['func'] == 'poly':
				c1['const'] = max(c1['const'], lq['const'])
			ccr = ccr[:-1]
	c2 = {'type':sec_q, 'const':x*nd['const']/2, 'func':'log'}
	ndr = {'type':'nand', 'const':nd['const']*(1 - x)}
	ccr.append(c1)
	ccr.append(c2)
	ccr.append(ndr)
	return ccr

# slowdown lemma:
# NTIME[n] \subseteq NAND-depth[cst log n] (with pading)
def slowdown(cc, cst):
	ccr = cc[:-1]
	nt = cc[-1]
	assert nt['type'] == 'ntime', f"Cannot apply the slowdown lemma to a non-NTIME class {nt}"

	nd = {'type':'nand', 'const':nt['const']*cst}
	ccr.append(nd)
	return ccr


# Replace NAND-depth[c log n] with TS[n^c]
def simulate(cc):
	ccr = cc[:-1]
	sc = cc[-1]
	assert sc['type'] == 'nand', f"Cannot apply simulation to class {sc}"
	ts = {'type':'ts', 'const':sc['const']}
	ccr.append(ts)
	return ccr

# Replace (Q c log n) TS[n^d] with TS[n^{d+c}]
def exhaustive_search(cc):
	assert len(cc) > 1, "exhaustive_search needs a class of the form (Q f(n)) TS[g(n)]"
	ccr = cc[:-2]
	qc, sc = cc[-2:]
	assert qc['type'] in 'AE' and 'func' in qc and qc['func'] == 'log', f"Cannot apply exhaustive search to quantifier class {qc}"
	assert sc['type'] == 'ts', f"Cannot apply exhaustive search to runtime class {sc}"
	ts = {'type':'ts', 'const':sc['const']+qc['const']}
	ccr.append(ts)
	return ccr

# TODO: handle coNTIME
def reinterpret_quantifier_ts(cc):
	assert len(cc) > 1, "reinterpret_quantifier_ts needs a class of the form (Q f(n)) TS[g(n)]"
	ccr = cc[:-2]
	qc, sc = cc[-2:]
	assert qc['type'] in 'AE', f"Cannot apply NTIME transformation to quantifier class {qc}"
	assert sc['type'] == 'ts', f"Cannot apply NTIME transformation to runtime class {sc}"
	nt = {'type':'ntime', 'const':max(sc['const'], qc['const'])}
	ccr.append(nt)
	return ccr

def pretty_print(cc):
	s = ''
	for c in cc:
		if c['type'] in 'AE':
			s += f"({c['type']} n^{float(c['const'])})" if c['func'] == 'poly' else f"({c['type']} {float(c['const'])} log n)"
		elif c['type'] == 'nand':
			s += f"NAND-depth[{float(c['const'])} log n]"
		elif c['type'] == 'ts':
			s += f"TS[n^{float(c['const'])}]"
		elif c['type'] == 'ntime':
			s += f"NTIME[n^{float(c['const'])}]"
		else:
			assert False, f'Problem with class {c}'
		s += ' '
	return s

def run_proof_annotation(ann, slow_c):
	sc = {'type':'ntime', 'const':Fraction(1)}
	cc = [sc]
	print(pretty_print(cc))
	cc = slowdown(cc, slow_c)
	print("\t\\subseteq", pretty_print(cc))
	for t, c, b in ann:
		if t == 'speed':
			cc = speedup(cc, c, b)
		elif t == 'slow':
			cc = slowdown(cc, slow_c)
		elif t == 'sim':
			cc = simulate(cc)
		elif t == 'ex':
			cc = exhaustive_search(cc)
		elif t == 're':
			cc = reinterpret_quantifier_ts(cc)
		else:
			assert False, f'Incorrect annotation type: {t}'
		print(f"({t},\t{c},\t{b})\t\\subseteq", pretty_print(cc))


if __name__ == '__main__':
	SLOW_PARAM = Fraction(900, 301)
	c = Fraction(2, 3)
	n = 209
	ann = [('speed', c, True), ('speed', c, False)]*(n//2) \
	+ ([('speed', c, True)] if n%2 == 1 else []) \
	+ [('sim', None, None), ('ex', None, None), ('re', None, None)] \
	+ [('slow', None, None), ('sim', None, None), ('re', None, None)]*(n-1)


	# ann = [('speed', c, False), ('speed', c, True)]*((n-1)//2) \
	# + ([('speed', c, True)] if n%2 == 1 else []) \
	# + [('sim', None, None), ('ex', None, None), ('re', None, None)] \
	# + [('slow', None, None), ('sim', None, None), ('re', None, None)]*(n-1)
	run_proof_annotation(ann, SLOW_PARAM)