# TODO

## Meeting with ryan : 16/05/2022

Goal: find super cubic size lower bounds.

- Does the bounded fan-in actually matter? Can we say something more general?
- What about formulas with parity gates vs #SAT ? Can we get a supercubic lower bound for #SAT or Parity-SAT?
- Can we use the result for monotone formulas ? See the russian paper.
- Can we do something to turn the depth LBs into size LBs? It looks like it needs to be SAT-specific, because of the result in the russian paper.

## Balancing arbitrary fan-in formulas

Interesting related: 
http://150.140.5.98/index.php/beatcs/article/viewFile/275/257
- Can turn arbitrary fan-in, d-depth, size s De Morgan formula into a fan-in 2 formula of depth d-1+ceil(log S) .
This means that we can turn "AC1" --> FORMULAS <-- into "NC1" formulas?
The only difference is a +1 in front of the log. 

Proof : https://web.vu.lt/mif/s.jukna/boolean/comment2.html

Technique : take the topmost gate (say, OR)
recurse on subgates (ANDs)
do a huffman encoding tree of the subgates, weighted by their size
Put OR gates at internal nodes of the tree.

The result is not alternating.
Maybe we can do it by adding negations, and enforcing stuff?
The position of the subformula F_i only depend on their sizes, therefore we can compute it in advance. Then, ask for not F_i instead of F_i (it is still an AC0-type formula).
We might need to add one gate at each step to enforce the alternation...
-> No, this does not work
What we can do however, is add useless alternations, and win at every layer change. Maybe we can win d ?
That would yield d + 2log(s) instead of 2(d+log s), naively.
depth alogn, size n^b => (a+ 2b) log n > 3.603 log n.
a = 1? => b > 1.301...
Constant depth: b > 2 cos pi/7. This is not very good... WE ALREADY KNEW IT GOD DAMMIT

## Meeting with Ryan 19/05 and other ideas

- What can we do for #SAT, \oplus SAT and SAT?
- Formula size? 
- Less restricted formulas? 
	-> Layered formulas?
	
- Result with xor gates/and gates: either SAT or parity SAT requires time more than n^c