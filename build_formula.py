import math

class BooleanFormula:
	def __init__(self, t, **kwargs):
		self.type = t
		self.neg = 'neg' in kwargs and kwargs['neg']
		if t == "OR" or t == "AND" or t == "NAND":
			self.left = kwargs['l']
			self.right = kwargs['r']
		elif t == "VAR":
			self.ind = kwargs['ind']
		elif t == "F":
			self.f = kwargs['f']
			self.values = kwargs['val']
		else:
			raise ValueError(f'found invalid type {t}')

	def __str__(self):
		symb = {"OR": " \\vee ", "AND":" \\wedge ", "NAND": " nand "}
		if self.type in symb:
			s = "\\left( " + str(self.left) + symb[self.type] + str(self.right) + " \\right)" 
		elif self.type == "VAR":
			s = f'x_{self.ind}' 
		elif self.type == "F":
			s = 'f_{ ' + ''.join('1' if x else '0' for x in self.values) + ' }'
		if self.neg:
			s = "\\neg " + s
		return s

	def eval(self, valuation):
		if self.type == "OR":
			res = self.left.eval(valuation) or self.right.eval(valuation)
		elif self.type == "AND":
			res = self.left.eval(valuation) and self.right.eval(valuation)
		elif self.type == "NAND":
			res = not (self.left.eval(valuation) and self.right.eval(valuation))
		elif self.type == "VAR":
			res = valuation[self.ind] 
		elif self.type == "F":
			res = self.f(*self.values)
		
		if self.neg:
			ares = not res
		else:
			ares = res

		# print("",ares, self)
		return ares

	def depth(self):
		if self.type in ["VAR", "F"]:
			return 0 
		else:
			return 1 + max(self.left.depth(), self.right.depth())

def big_and(v, neg=False):
	n = len(v)
	base = BooleanFormula("VAR", ind=0, neg=v[0] == 0)
	for i in range(1, n):
		base = BooleanFormula("AND", l=base, r=BooleanFormula("VAR", ind=i, neg=v[i] == 0), neg=i == n-1 and neg)
	return base

def big_and_odd(v):
	n = len(v)
	base = BooleanFormula("VAR", ind=0, neg=v[0] == 0)
	for i in range(2, n, 2):
		base = BooleanFormula("AND", l=base, r=BooleanFormula("VAR", ind=i, neg=v[i] == 0))
	return base

# this functions takes pairs (index, is positive)
def balanced_big_and(v, neg=False):
	n = len(v)
	if n == 1:
		ind, pos = v[0]
		return BooleanFormula("VAR", ind=ind, neg=(not pos) != neg)

	m = n // 2
	ll = balanced_big_and(v[:m], False)
	rr = balanced_big_and(v[m:], False)
	base = BooleanFormula("AND", l=ll, r=rr, neg=neg)
	return base

def new_build_or_and_formula(f, n, l=[], is_or=True):
	if n == 0:
		app_f = BooleanFormula("AND", 
				l=BooleanFormula("F", f=f, val=[bool(x) for x in l]), 
				r=balanced_big_and([(i,l[i]) for i in range(len(l))]))
		other = balanced_big_and([(i,l[i]) for i in range(0, len(l), 2)])
		notx = balanced_big_and([(i,l[i]) for i in range(len(l))], neg=True)
		and_other = BooleanFormula("AND", l=other, r=notx)
		return BooleanFormula("OR", 
				l=app_f, 
				r=and_other)
	f1 = new_build_or_and_formula(f, n-1, l+[0], not is_or)
	f2 = new_build_or_and_formula(f, n-1, l+[1], not is_or)
	return BooleanFormula("OR" if is_or else "AND", l=f1, r=f2)


def form(a,b,c,*args):
	# res = b == (a and c)
	res = b or (a and c)
	return res


def test_f(phi, f, n, l=[]):
	if n == 0:
		# print(l)
		return phi.eval(l) ==  f(*l)
	return test_f(phi, f, n-1, l + [False]) and test_f(phi, f, n-1, l + [True])

if __name__ == '__main__':
	for N in range(3,14):
		tmp = new_build_or_and_formula(form, N)
		# print(test_f(tmp, form, N))
		print(tmp.depth(), N + math.ceil(math.log(N, 2)))