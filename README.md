cs320-notes
===========

jan 3
=====


Jan 3
1.1 The Stable Matching Problem
===============================

Goal: given M Men and W women.  Each man ranks all women and every woman ranks all men.  We want to order the men and women into pairs such that:
	1. every man and woman appears in exactly 1 pair
	2. there is no pair of pairs (m, w) and (m', w') such that m prefers w' to w and w' prefers m to m'.  In that case it would be better to form the pair (m, w')

Definitions:  /\/\ = { m_1, ... , m_M } set of men
			  \/\/ = { w_1, ... , w_W } set of women

			  then /\/\ x \/\/ = { (w, m), w in \/\/, m in /\/\ } set of all ordered pairs of man and women form /\/\ and \/\/.

			  A maching J is a subset of \/\/x/\/\, and that every man m in /\/\ and every woman in \/\/ appear in at most one pair ( some may be unpaired ).

			  A perfect matching J' is a subset of \/\/x/\/\ such that each w in \/\/ appears in exactly one pair.

A pair (w',m) in \/\/x/\/\ is called an instability w.r.t a matching J if (w',m) is not in J but (w,m) and (w',m') are in J and yet m and w' prefer each other to their assigned partners.

A matching S is stable if (a) it is perfect and (b) there is no instability w.r.t S.

Goal: Given sets \/\/ and /\/\, find a stable matching.


// ma algorithm: give every woman her first pick
	// if two women have the same first pick, resolve by picking woman man prefers for that pair and give remainin woman her 2nd pick (and so on)
	// if there is ever a situation where womanA wants a man as her ith pick and womanB wants the same man as her jth pick give to woman with higher preference, resolve tie with mans preference.

her / Gale-Shapley Algorithm
	let all m in /\/\ and w in \/\/ be free / unpaired
	while there is a free woman that isn't paired to any man yet {

		w takes the highest ranking man that isn't proprosed to yet (m) and checks state {
			if ( he's already engaged ) { 
				she just proposes
			} else { 
				if ( he prefers her m over his m' ) {
					pair (m,w)
					and put w' free
				}
		} 
	}

	pree sure its the same :>>

In the problem there is symmetry w.r.t the men and women but our choice of algorithm introduces an asymmetry w.r.t the men and women.

When a man changes pairs his pairing inproves for him.  Whereas for a woman it gets worse each time.



Defining Patterns of an Algorithm
	in a finite list of instructions
	each instruction can be described properly (?)
	arbitrarily form an initial state and initial input, the instructions describe a completion of a finite number of successive states eventually producing an output and terminating in a finish state.
	each state only depends on the inputs and results of previous states
	output is reached after a finite number of steps (no infinite loops)

jan 8
=====
Jan 8 


Stable Matching Algo
====================
set all m in M and w in W to free
while a free woman has not yet proposed to every man:
m <- highest ranking man w hasn't proposed to yet
if m is free:
pair w and m
else:
w' <- current fiancee of m
if m prefers w to w':
set w to free
pair w and m

1.1.1 TIME COMPLEXITY
=====================
observation 1. m remains paired and his partners get better over time
observation 2. the sequence of men to which  w proposes to gets worse

Theorem: The stable matching algorithm terminates after at most N^2 iterations of the while where N = M = W.

Proof: at every iteration of the while-loop a woman proposed to a man she hasn't proposed to yet.  Given that there are N men, each woman makes at most N proposals, as there are N women, we thus have at most N^2 iterations of the while loop.

The total execution time also depends on:
	(a) How many steps it takes to identify an unpaired woman
	(b) How many steps it takes a woman to decide whom to propose to 
	(c) How many steps it takes a man m to decide if he prefers woman w to w'

How to optimize those (in time if not in space ...)
	(a) Keep a list of unpaired women
	(b) Each woman has a list of men sorted in decreasing order, maybe a stack, dont want men she's already proposed to in there.
	(c) Each man has an array index my woman's number assigning them a value, and an index naming his current partner.

1.1.2 CORRECTNESS OF ALGORITHM
==============================

Lemma.1 If we find a lady who is unpaired, then there will be at least 1 man who she hasn't proposed to yet.
Proof: according to observation 1, if Woman w has proposed to every man, then every man is engaged.  Since the number of women (W) is equal to the number of men (M), this implies that every woman is engaged.

Lemma.2 The set J C \/\/ x /\/\ returned by the algorithm is a perfect matching.
Proof: The algorithm terminates if every woman is paired, we also know that every woman is paired to at most 1 man at any time.  So, at the end of the algorithm, every woman is paired to exactly one man.  Because N = M = W, this imples that every man is paired to exactly one woman.

Theorem The matching returned by the algorithm is stable.
Proof:  [ by contradiction again ] 
	Suppose the algorithm returns an instability wrt the matching, ie. a pair of pairs (w,m) and (w',m') where m prefers w' to w and w' preferns m to m'.  

	From the algorithm we know that the last proposal of w' was to m', otherwise they would not form a pair.
	Did w' propose to m?
	(1) If not, because she actually ranks m > m', and ladies propose to men in order of preference we have a contradiction.
	(2) If so, if w' proposed to m and yet is no longer paired with m, then at some point she must have been kicked out by a woman that m preferes to her.  Either this woman, w'' is his current pair, or was kicked out by someone even better, and likewise w'' could have been kicked out by someone even better, but in the end the point is the last woman w is prefered to the first, w', which is a contradiction.

	Therefore there is no way that an instability can possibly exist and the matching is stable.

2. ASYMPTOTIC NOTATION
======================

Motivation: we want to find out how an algorithm's running time grows as a function of the input size.  Typically, we are interested in the worst-case running time of an algorithm.

Definition: step in the algorithm = assigning a value to a variable etc.

Goal: Given an algorithm, generally as pseudo-code, specify the running time ( in steps ) as a function of the input size n.

We want to capture hte running time in a way that is 
	- insensitive to constact factors
	- loswer order terms
	- hardware independent

2.1 ASYMPTOTIC UPPER BOUNDS big-O
=================================

Motivation: Given an algorithm specified in pseudo-code which requires at most T(n) to complete for an input of size n (an Integer), T: Ints -> pos_Reals, find a function f: Ints -> pos_Reals which, if multiplied by a real constant c > 0, provides an upper bound to T(n) for sufficiently large vales of n, for all integers n.

In other words, find a function f: Ints -> pos_Reals such that:
			 T(n) <= c * f(n),  for all ints n > n_0, c>0 real

Example. T(n) = 7n^2 + 5
	What is an asymptotic upper bound on T(n)?
	We could, for example, choose f(n) = n^3
	Because T(n) = 7n^2 + 5 <= 7n^2 + 5n^2 <= 12n^2 <= 12n^3 = c*f(n) fpr all  ints n >= 1.

jan 10

2.1 ASYMPTOTIC UPPER BOUNDS
===========================

T(n) = the worst-case number of steps the algorithm requires to complete for an input of size n.

Def: let T(n), T: Int -> Reals, describe the worst-case running time of a given algorithm as a function of input size.
We say T(n) is of order f(n), O(f(n)), if T(n) is asympotically upper bounded by f: Int->Reals, ie there is a constant real c  and n_0 such that T(n) < c*f(n) when n > n_0.  
We then write T(n) = O(f(n))

2.1 ASYMPTOTIC LOWER BOUNDS (OMEGA THING)
=========================================

Def: Let T(n) be defined as before.  We say that T(n) is OMEGA(f(n)), ie we say that T(n) is asymptotically lower bounded by f(n): int -> real, if there is a constant c in R and n_0 such that:
	T(n) >= c*f(n) when n >= n_0
we also say:
	T(n) = OMEGA(f(n))

Group Work: Find an asympototic lower bound for T(n)

2.3 ASYMPOTOTIC TIGHT BOUNDS THETA(phi)
=======================================

Motivation: We would like to know a precise decription of an algorithm's worst-case runnng time.

Definition: We say that f(n) is an asympotically tight bound for T(n) and we say T(n) is     THETA(f(n)) if T(n) = O(f(n)) = OMEGA(f(n)) (for the same f but sure different n_0)

Ex.  Since we have shown that T(n) = 7n^2 + 5 has a lower bound f(n) = n^2 and an upper bound f(n) = n^2, we have already that T(n) = THETA(f(n)).

2.4 PROPERTIES OF ASYMPTOTIC GROWTH RATES
=========================================

Theorem: let f,g : int -> R be two functions for which:
	lim n-> inf f(n) / g(n) = C, where C>0 in R
Then we have that g(n) is a tight bound for f(n), ie f(n) = THETA(g(n))

Proof: 
	if lim f(n)/g(n) = C, then we have that there exists some n_0 such that:
		C/2 <= f(n)/g(n) <= 2C, for n > n_0
	That is,
		f(n) <= 2C*g(n) for n>n_0, therefore f(n) = O(g(n))
		f(n) >= C*g(n)/2 for n>n_0, therefore f(n) = OMEGA(g(n))
	Therefore f(n) = THETA(g(n))

--> you could do the same for g(n), just 1/ everything.

Lemma: if a function f is asympototically upper-bounded by g and g in turn is asymptotically bounded by h, then f is asymptotically upper-bounded by h.  Likewise for asympototically lower and therefore this also applies to asymptotically tight bounds.

	In other words:
		(a) f=O(g) ^ g=O(h) -> f=O(h)
		(b) f=OMEGA(g) ^ g=OMEGA(h) -> f=OMEGA(h)
		(c) f=THETA(g) ^ g=THETA(h) -> f=THETA(h)

	Proof: 
		(a) we have there exists n_0 and c1 such that for all n>n_0 f < c1*g and also there exists n_1 and c2 such that for all n>n_1 g<c2*h, which implies that c1*g < c1*c2*h.
		So take n_2 to be max(n_0, n_1) and we have for all n > n_2 f < c1*g < c1*c2*h = c3*h.  Which implies that f is O(h).
		(b) see (a) except reverse all the inequalities on f and g and h ...
		(c) we have the same assumptions as (a) and (b) therefore we have the same results as (a) and (b), ie we have f=O(h) ^ f=OMEGA(h) -> f=THETA(h)

Lemma: f=O(h) ^ g=O(h) -> f+g=O(h)

	Proof:
		we have f<= c1*h(n) for all n>n_0
		and have g <= c2*h(n) for all n>n_1
		so f + g <= c1*h(n) + c2*h(n) = (c1+c2)*h(h) for all n>max(n_0, n_1)

Lemma: Given integer k, and k fucntions f_i : N -> R, i in {1,2, ..., k}
	with f_i = O(h), then
	SUM f_i = O(h)

	Proof: 
		SUM f_i(n) <= SUM c_i*h(n) = ( SUM c_i )*h(n) 

Lemma: Given g = O(f), then f + g = O(f)

	Proof:
		Obviously f is O(f), therefore since we have g=O(f) by the lemma 2 lemma's ago we have f+g = O(f)

Lemma: Given g = O(f), then f + g = THETA(f)
	
	Proof:
		By the previous lemma we have that f(n) + g(n) = O(f).
		additionally we know that f(n) <= f(n) + g(n) since all functions > 0
		therefore f(n) + g(n) = OMEGA(f)
		therefore f(n) + g(n) = THETA(f)


jan 15
======
Jan 15

2.5 ASYMPTOTIC BOUNDS FOR SOME COMMON FUNCTIONS
===============================================

try not to forget what a POLYNOMIAL is ok.
lemma: let f be a polynomail of degree d, then f=(n^d)
	proof: let f(n) = SUM a_in^i.  We can define f_i(n) = a_in^i.  Then for every f_i:
		a_in^i <= |a_i|n^i for all integers n, and |a_i| in Reals.
	We also have, for every f_i:
		a_i n^i <= |a_i| n^i <= |a_d|n^d, thus f_i = O(n^d), thus f=O(n^d) by additivity proved before.

likewise with LOGS / LN / LG
lemma for every b, r>1 in reals,and n>0, we have log_b(n) = O(n^r)
Note: 	log_b(n) = x in reals is the solution to n = b^x,
		log_b(n) = log_x(n)/log_x(b),
		log_c(n) <= n

also EXPONENTIALS
lemma: n^d = O(n^n) for every integer n>1, reals r>1 and d>0, ie. exp > poly always.

2.6 SURVEY OF COMMON RUNNING TIMES
==================================
2.6.1 ALOGIRHTMS THAT REQUIRE O(N) IE. LINEAR TIME
===================================================
example. we have two sorted arrays of numbers, A = [ a1, a2, ... an ], B = [ b1, b2, ... bn ].
find an efficient algorithm to merge thesse number into one sorted list.  assume ascending order

pointer into each array, compare current value of both, add smaller to sorted list and inca.
(consider end of list loser in any comparison)

hers:
while we haven't reached the and of any list {
		let ai and bj be the next elements pointed to
		append min{ ai, bj } to list C and advance corresponding pointer
}

the algorithm is of O(n).  Proof:
	The resulting list C has 2n elements.  Each element required a single operation (comparison) to be added to C.  The while-loop is thus executed at most 2n times.  therefore the running time is O(n)

2.6.2 ALOGIRHTMS THAT REQUIRE O(N^2) IE. QUADRATIC TIME
=======================================================
example: Given a set of n points (xi, yi) in R^2, find the pair of points i and j i =/= j with the smallest eulidian distance, d = d((xi, yi), (xj, yj)) = sqrt( (xi-xj)^2 + (yi - yj)^2 ) >= 0

observation: 
going through the points and making all new comparisons that you need to to that point we have
(n-1) + (n-2) + (n-3) + ... = n(n-1)/2 = the number of unordered pairs as you'd expect.

Algorithm:
	for each i from 0 to n, take input point (xi, yi) {
		for each j from i to n take input point (xj, yj) {
			compute dij
			if dj is smaller than the current minimum distance d, replace with dj
		}
	}

The worst case running time is O(n^2) as we have two nested for-loops which each require O(n) time and the operations in the inner-most scope require constant time.

2.6.3 ALOGIRHTMS THAT REQUIRE O(N^3) IE. CUBIC TIME
===================================================
example.
given n subsets Si of the set of integers { 1, 2, ... n } first out if any pair of subsets Si Sj are disjoint. ie Si intersect Sj = empty set.

algorithm:
	for each set Si {
		for each set Sj i=/= Si {

		for each element p in Si {
			 check Sj for p:
			 if p in Sj break with failed
		}
		if not failed (if no elements of Si were found in Sj) 
		then we have found our disjoint set
		}
	}

The worst case running time is O(n^4) as we have 3 nested loops each requiring O(n) time and an O(n) operation inside of that.  However if we have an array for out sets or something and are assuming that the inner most scope can be completed in constant time then it's O(n^3).

2.6.4. ALOGIRHTMS THAT REQUIRE O(N^K) TIME
==========================================

Ex.  given a graph with n nodes, check if it contains an independent set of size k <= n, ie a set of k nodes, where there are no edges between any pair of nodes.  

Algorithm: 
	for all subsets S of size k nodes {
		 check if S is independent
		 if so: 
		 	then return true
	}
	return false


// is this any better? recursive
for each node {
	try picking another node indenpendent to it and recurse
		return if you fail with this node dropping it from the nodes considered on with the previous node
}


how many sets of size k are there to be considered?
num = C (n,k) = (n!)/(n-k)!k! = (n)(n-1)...(n-k+1)/(k*(k-1)*...1) <= n^k/k!
also she's saying <= n!/k! <= n^k/k! which is true asymptotically with k.

Inside the for-loop, each k-node sub-set is treated for independence, this requires investigating C(k,2) pairs which is O(k^2).  The for-loop is executed at most n^k/k! times.  As we can view K as a constant, the algorithm is overall O(n^k).

2.6.5 ALGORITHMS THAT REQUIRE BEYOND POLYNOMIAL TIME
====================================================

ex. similar to 2.6.4, but now the task is to find an independent k-node set of maximal k <= n.

Algorithm:
	for each subset s of n nodes {

		check if S is an independent set
		if yes and S is larger than the previously found subset {
			record the size of S as the current maximal set
		}
	}

We now need to consider all subsets S of n nodes:
there are :

SUM C(n, k) from k=0 to n
= SUM C(n,k) (1)^k (1)^(n-k) = (1+1)^n (binomial)
							 = 2^n

the for-loop is of order O(2^n) each subset requries at most O(n^2) time to check for indepence, the algorithm thus requires O(2^n*n^2) time

jan 17
======
jan 17

2.6.6 ALGORITHMS THAT REQUIRE SUB-LINEAR TIME, IE O(LOG(N))
===========================================================

example.  supposed we are given an array of n integers already sorted bumbers.  the task is to find out if a given number b is stored in the list or not.

Binary search -> log(n) time

Algorithm
	If p is smaller than the smallest entry of the array or lager than the largest entry, it cannot be part of hte array.

	Else: proble the middle entry of the array.  If p=q we are dne.
	if p < q, we probe the remaining array to the left of q.
	if p > q, we probe the remaining array to the right of q.


At every step of the algorithm, we are halving the length of the remaining interval.  after k steps we have an interval (1/2)^k * n in siace.  If we want this interval length to be on constant size, for real pos C, we need the following number of steps:

(1/2)^k * n = C <--> n = C * 2^k <--> lg(n) = lg(C) + k

ie for C = 1, k = lg(2)

We require O(lg(n)) steps until we can finish the task in constant time.

2.6.7 ALGORITHMS THAT REQUIRE O(N LOG(N)) TIME
=============================================

example. given a set S which contains an even number of numbers that we want to sort.

idea: parition S into two distinct sub-sets, S1 and S2 of size n/2 each, sort the numbers in each subset and then recombine the sorted lists.  (see 2.6.1) Apply recursively.

Size of problem in layer n:
cn
2 * (cn/2)
4 * (cn/4)
etc.

(decision tree)

so size of layer is constant, so work per layer should be consant, and we just need that times the number of layers, which there are log(n) of.

Let T(n) denote the worst-running time of the recursive algorithm, we have:
	T(n) <= 2*T(n/2) + O(n), recursively

2*[ 2*[ 2*T(n/8) + O(n/4) ] + O(n/2) ] + O(n)  ~= n log(n) times coolcool

The recursive algorithm requires O(nlog(n)) time as we have O(log(n)) layers each requiring O(n) time, see 2.6.1.


3. GREEDY ALGORITHMS
====================

Attempt of a definition: An algorithm is called greedy if the final outcome of the algorithm is retrieved via small steps, where each step aims to optimize based on the locatal information at that time.

3.1 INTERVAL SCHEDULING
=======================

problem: Given a set S of intervals N, ie S = { (si, fi) : n = 1,2,..,N, si < fi }

task: Find a subset T <= S such that: 
	no pair of intervals overlap, ie.
		for all pairs i,j we have fi < sj or fj < si
	then T is called a compatable set of intervals

	there is no other compatable set T' larger than T.

Definition: R = set of intervals in S that have not yet been considered
			A = set of selected intervals of S

Interval scheduling algorithm #1:
	Set R = S, and A is empty

	while R is not empty:
		choose interval i in R whose fi is the smallest
		add i to A
		remove all intervals in R that are incompatible with endpoint i

Properties of this algorithm: correctness
Claim: the algorithm returns a compatable set of intervals A <= S.
this follows directly from the algorithm, the bit where we remove conflicts

Theorem: The algorithm returns an optimal sub-set A <= S.

Proof: (by contradiction)
assume that the sub-set A <= S that the algorithm returns is not optimal, ie. that there is another sub-set B <= S of compatible intervals that is strictly larger than A.  In other words:

A = { ni,fi : i=1,2,...,k }
B = { n1,fi : i=1,2,...,m } and m > k.

jan 22
======
jan 22

PROOF: that our algorithm produces the optimal set

IDEA: proof by contradiction, we will assume our algorithm produced set A
	A = { si, fi | i in {a1, a2, ... , ak}} k < n
while there exists a set B:
	B = { si, fi | i in {b1, b2, ... , bm}} with k < m < n
So B is better than A.

Lemma: Let the sequence of interval indicies in A ie. a1, a2, ... ak, correspond to the order in which these intervals are added to  in the algorithm.  Let the sequence of interval indicies in B, ie. b1, b2, ... bm, correspond to the natrual left to right order.

	Then for indicies r <= p -> f(ar) <= f(bp) where r in { a1, a2, ... ak } and p in { b1, b2, ..., bm }

Proof by induction:
	Base Case: The statement f(a1) <= f(bp), for p in { b1, b2, ..., bm } is correct as the algorithm picks as its first interval the one with the smallest end-point.

	Inductive assumption: (r-1) -> r
	Assume correctness of the statement for (r-1) and, based on this, we will show correctness of the statement for r.

	Given f(a_r-1) <= f(b_r-1) and that B is a compatable set and it's indicies are ordered from left to right ie f(b_r-1) < s(br) so we conclude that f(a_r-1) < s(br).
	Because of this, interval (s(br), f(br)) is in the set R of intervals that are still available.  when the algorithm selects (s(ar), f(ar)).  As the greedy algorithm selects the leftmost end-point, we get f(ar) <= f(br), ie it picks that interval of B's or an even better one.

PROOF OF THEOREM (continued):
	Choose the same indicies ordering for A and B as in the previous lemma.  Remember, we assume k < m.  According to the lemma, this implies that
		f(a_k) <= f(b_k) < s(b_k+1)
			(an interval b_k+1 must exist in B, because k<m, ie. there has to be at least k+1 intervals in B)

		This implies that the set R in the algorithm was not empty when the algorithm terminated and returned A.  This is a contradiction to k < m above.  So, k >= m holds and this implies that A was optimal after all. 


WORST CASE RUNNING TIME OF THE ALGORITHM: (see prev day for def)

Claim 1: the worst-case running time is O(n^2).
Proof: The while loop requires O(n) steps and the statement within the while requires at most O(n) steps, ie. overall we have O(n^2).

speed up: keep all your things sorted why would this even not already be the case you fool.

Algorithm: A = the empty set, R = S,
	sort R by increasing finishing time.  (this takes O(nlogn))
	xmax = -inf
	For each interval i in R {
		if (s(i) > xmax){
			add interval i to A
			xmax = f(i)
		}
		return A
	}

Note that the outer loop is still n, but the inside is fixed time now, so the whole thing is O(nlogn) just from the sorting.

Overall the algorithm requires O(nlogn).  the sorting and selecting only things further right than the previous rightmost interval ensure that we end up with a list of compatable intervals in A.

3.2 APPLICATONS OF GREEDY ALGORTITHMS

3.2.1 DATA COMPRESSION

Goals: given a string X over some alphabet, we want to replace each character in it by a sequence of bits so that:
	The resulting string is as short as possible
	we can recover the original string X from the string of bits.

Example. X = abacbaada S = { a, b, c, d }
Brute force: a -> 00, b -> 01, c -> 10, d -> 11
then we have A = 000100100100001100

Def: a fixed length code maps all elelemnts of S to a bit-string of the same length.

Given an alphabet S with K = |S| elements, how long does a fixed-length code have to be to encode this?

Answer: We can encode 2^m = k characters using bitstrings of m bits, so we require ciel(lg(S)) bits in each string to encode S distinct characters.

Def: a variable length code maps characters from S to strings of bits of variable length.

Example. X = abacbaada S = { a, b, c, d }
a -> 0, b -> 10, c -> 110, d -> 111
then A = 010011010001110

Potential Problem: Decoding becomes ambiguous if the bit string of one character is the prefix of the bit string of another character.

Definition: A prefix code for an alphabet S is a function f that maps every element in S to a bit-string such that for all x,y in S, x =/= y, f(x) is not a prefix of f(x).

Decoding using a prefix-code:
	Read bit-string of X from the start until an encoding f(x) for some x in S is found, then we may translate this back into X and continue until the end of the bit-string is reached. 

Visualization: (see prevs example)

						. <-- root node, decoding begins
					 0 / \ 1
					 A     .
					 	0 / \ 1
					 	B    .
					 	  0 / \ 1
					 	  D     C  

					 	  Note that you can place any letter everywhere the number of them is what decides the max length of these strings.  So we are free to pick the shortest strings for the most common characters.

Assume in the following: We may need stirng X to determine the frequency F (0<=F<=1) of each element x in S.

Goal: We want to find a prefix code f, such that for a given text X and alphabet S that the length of the text,
	L = SUM_{alphabet} F(ci) * |f(ci)|  <-- frequency of letter times size of letter string for 										all letters = total length.



jan 24
======
jan 24

HUFFMAN'S ALGORITHM
======================

GIVEN: string X of characters S and frequencies f(x), for all x in S
GOAL: determine an optimal prefix code p.

while not through with alphabet: 

	if we have |S| = 2:
		choose 0 to encode one character and 1 for the other
	else: 
		we identify y* and z* to be the 2 characters with the lowest frequency
		define a new alphabet S' by removing y* and z* from S replacing with w (frequency(w) = frequency(y*) + frequency(z*))
		recursively construct a prefix code for S' with binary tree T'

		define a prefix code for S as follows:
			Start with T'
			take the leaf labelled w and add y* and z* as children


Definition: The prefix code thus determined is called Huffman's code

Example:

S = { a, b, c, d, e } and some string X with frequencies: 
	f(a) = 0.32, f(b) = 0.25, f(c) = 0.20, f(d) = 0.18, f(e) = 0.05


So first z* and y* are e and d, so replace with w, f(w) = 0.23
	
	w
   / \
  e   d

 We have { a, b, c, w } then z* and y* are c and w, so replace with m, f(m) = 0.43

 	  m
 	 / \ 
 	w   c
   / \
  e   d

 We have  { a, b, m } now z* and y* are a and b, so replace with n, f(n) = 0.57

 	  m
 	 / \ 
 	w   c
   / \
  e   d

    n
   / \
  a   b

  We have { n, m } so the if clause applies and we define n = 0, m = 1

  	     k
  	    / \
  	   /   \
   	  m     n
 	 / \   / \
 	w   c a   b
   / \
  e   d

apply 1's and 0's to each branch, and the path down to any leaf then specifies a prefix code.

Note: the optimal prefix code is not unique (usually), because the two edges underneath each node in he correpsonding tree can be labelled 0 (left) 1 (right) or vice versa.

Claim 1: There is an optimal prefix code in which the two characters with the lowest frequency have encodings differing only in the last bit.

Proof: ommitted. see class notes.

Definition: The length of a prefix code p for string X, alphabet S and frequencies f(x) for all x in S, is defined as:
	SUM f(xi)|p(xi)| <--- the sum over all alphabet chars of their length * frequency in string

Definition: The length of tree T for encoding p:
	length(T) = SUM f(xi)|p(xi)|  <--- sort of total path length weighted by frequencies

Claim 2: Given a prefix tree T that satisfies claim 1 where the two letters with the lowest frequency are neighbouring leaf nodes.  If we remove the leaves of x and y and replace their parent node by w with freqrency f(w) = f(x) + f(y), then we obtain a new tree T' and alphabet S' with
	length(T') = length(T) - f(w)

NOTE: parent node is already as you say sans any replacing, however it does become a leaf node and so enter into our sum.  So really this should read remove x, y the lowest 2 frequency dudes.

Proof: length(T) = SUM_S f(xi)|p(xi)| = SUM_Snotxy f(xi)|p(xi)| + f(x)|p(x)| + f(y)|p(y)|
		           (pulling out x and y, the lowest 2)
				 = SUM_Snotxy f(xi)|p'(xi)| + ( f(x)+f(y) )|p'(w)+1| by *
				   (sum the same for all non xy bits switch to ')
				 = SUM_S'f(xi)|p'(xi)| + f(w)
				 = length(T') + f(w) = length(T)


* |p(x)| = |p(y)|
  = |p(w)+1|
  = |p(w')+1|


Theorem: Huffman's algorithm generate an optimal prefix code.
Proof: By contradiction, Supposed the algorithm produces a suboptimal prefix code with corresponding tree T and suppose that S with |S| > 2.  There is an optimal tree z such that the length of this optimal tree z, st. length(z) < length(T), where the two letters z and y with lowest frequency are sibilings (claim 1).  Replace the parent node of x and y with w such that 
f(w) = f(x) + f(y) in both z and T and alphabet S.  We thus get new trees z' and T' and a new alphabet S' such that (claim 2):
	length(T') = length(T) - frequency(w)
	length(z') = length(z) - frenquency(w)

becuase length(z) < length(T) (by assumption, she says claim 1), we have length(z') < length(T') which contradictions the optimality of T' as a prefix code of S'.  

(Except no iductive assumption was made here seems to be a mistake?)

3.2.2 FINDING SHORTEST PATHS IN GRAPHS
======================================

Assuption: We are dealing with directed graphs
Definitions: A graph G = ( V, E, s, t) consists of 2 sets V (verticies or nodes) and E (edges) and two mapping functions s: E -> (source) and t: E -> V (target).

S(e) in V ------- e, l(e) ------> T(e) in V

A graph is finite if V and E are finite.  A weighted graph (G, l) is a graph G = ( V, E, s, t) with a function l: E->R^+ (called length).  Two nodes in a graph are adjacent if there is an edge e connecting them.

A path p of m in N edges in a graph G is an m-tuple = (e1, ..., em ) of edges e in E, such that t(ej) = s(ej+1) for all j in { 1, ..., m-1 }.  The source and target of path p are s(p) = s(e1) and t(p) = t(em) and p is said to stat in s(p) and finish in t(p).

This definition doesn't fit with the above, but who cares!  A path of 0 edges is just the node  s(p) = t(p) = p in V.

The set of paths of m in N edges in G is called G^m.  
If G is a weighted graph, l(p) = SUM_m l(ei) is the length of path p.  
A simple path is one in which every node occurs at most once.

A simple cycle is a path that starts and ends at the same node, where every edge appears at most once except for the start/end nodes which appear exactly twice.

A graph is called undirected if every edge from a to b has a corresponding edge from b to a of the same length, otherwise the graph is directed.

An undirected graph is connected if there is a path between any two nodes in the graph.

An undirected connected graph is called a tree if it does not contain any cycle.  (you can comb a tree)

jan 29
======
jan 29

DATA STRUCTURES TO REPRESENT GRAPHS
===================================

Definition: the adjacency matrix of a graph G is a square matrix 
	A = (a_ij) (i == row, j == columb)
	of size | V |^2, where every entry a_ij is a number n in N_0 which corresponds to the number of edeges in G from v_i to v_j.

	// key thing about her adj matricies is that she's counting num edges between verticies.


GOAL: given a directed and weighted graph G = (V,E,s,t), a length function l, and a node (so-called start node) s' that has a path to every other noce in the graph.  Determine the shortest path from this node to any other node in the graph.

KEY IDEA:
	Step 1. Find a clever algorithm to calculate the shortest distance between s' and an node of G.
	Step 2. Find the corresponding shortest paths connecting s' to any other node.

	Start: L = {s'} d{s'} = 0

	Next: find the shortest distance to unexplored nodes by using known shortests distances to explored nodes:

		For each node s in V/J determine the shortest path within L from s' to a node u in J, followed by exactly one edge from u to v.

		And set
			d(v) = min (over u in L_v) { d(u) + l(v,u) }
			where L_v is the subset of nodes in L with a single edge to v.

			pointer p(v) = argmin (over u in L_v) { d(u) + l(u,v)} in S_v 
			argmin beging the 'u' giving you the minimum distance


Dijkstra's Algorithm:
For each node u in the graph G, we store a distance d(u).
Start: L = { s' } and d{ s' } = 0.

While( L < V (strictly)) {
		select a node v in V/L which has a direct edge to a node in L and where the distance:
		d(v) = min(u in L_v) { d(u) + l(u,v) } is minimal
		p(v) = argmin(u in L_v) { d(u) + l(u,v) }

		merge v with L and assign it d(v)
}

As we keep track of the pointers p(v) for evert node v that is bing added to L, we can, at the end of the algorithm, recover the shortest paht P_v between s' and v be following teh poiners from p(v) back to s' and reversing the order of the encountered edges.

Dijkstra's algorithm: proof of correctness
Idea: Proof by induction on size of L.

	Induction start: To begin with L = { s' } ie | L | = 1
					The claim that we obtain the optimal distance d(s') = 0 for the start node is correct.

	Induction step: k -> k+1
					Suppose the claim is correct for L with |L| = k, k > 1, we need to show that the correctness of the claim for k+1 follows.

	let v be the node that we add to L with |L| < k.  Let (u,v) be the final edge of the corresponding optimal path P_v.
	We know that P_u is the optimal path for every u in L and d(u) the corresponding shortest distance.

	Idea: We now consider any other path P'_v from s' to v and show that this path is at least as long as P_v.  In order to reach v, the path P'_v must leave L somewhere.

	Define 
	y: first node in the P'_v that is not in L
	x: node just before y in P'_v, ie x in L

	Suppose that P'_v is shorter than P_v.  If this were correct then the algorithm would have added node y to L via the edge (x,y) in iteration k+1 rather than adding node v.  as this did not happen, we can conclude that
		d(y) > d(v) which imples that P'_v is longer than P_v. 



Feb 12
======
Feb 12


DIJKSTRAS RUNNING TIME
======================

Recall defs: V = verticies / nodes, L = visited nodes, V\L = unvisited nodes

Recall the step in the algorithm:
	- select the node v in V\L which is connect by one edge to a node in L and where the following distance is minimal:
		distance(v) = min_u in L(k-1) { distance(from s' to u) + l(u,v) }
		(that is the total distance from s' through to a point in V one away from v to v itself)
		(min_u in L(k-1) just means the minimum of the value in {} checked for all u that were in the set L on the k-1th iteration)

We would like to optimize the above step.

Observations:

1. the whole loop requires (n-1) iterations for a graph with |V| = n nodes beacuse each iteration moves a node from V\{s'} to L. (where by V\{s'} she means the set of all nodes except for the starting node which starts out as visited)

2. How do we efficiently select the next node to be added to L?
	- on any iteration k we can:
		- remember the distances values we have already calculated
		distance(v) = min_u in L(k-1) {  d(u) + l(u,v) } for every u in V\L at any time
		- order nodes in V\J in a heap-based priority queue with distance(v) vlaues as keys
		- in iteration k, add winning node L(k) = L(k-1) union { v } (<--- the kth L is just the K-1th L with v added) and remove v' and d(v') from the priority queue.

	- at iteration k+1: consider all nodes in V\L(k)
		- if (v',v) in E (E = set of edges) then we may need to assing a new value to distance(v) by computing 
			distance_k+1(v) = min{ distance_k(v), distance_k(v')+l(v',v) }
		  else distance_k+1(v) = distance_k(v)

3.  Throughout the algorithm, we need to change a key at most once for every edge in the graph, whenever a node at the end of that edge is added to L.

4.  For a graph with |V| = n nodes, ie. at most n elements in the priority queue, we need at most O(log(n)) time to 
		- insert or delete an element
		- change an element's key
		- extract an element with minimum key

CONCLUSION: For a graph with |V| = n nodes and |E| = m edges, the algorithm requires O((m+n)log(n)) time.

Proof: Based on observations 3 and 4 we require at most m*log(n) time to update at most m keys in the priority queue, each of which take log(n) time.
Based on observations 1, 2 and 4, we require at least n*log(n) time to delete at most n nodes from the queue, each again costing log(n) time.



3.2.2 MINIMUM SPANNING TREES
============================

Recall: an undirected, connected graph G is called a tree if it does not contain a cycle.

Definition: A spanning tree in a graph G is a tree that contains all nodes in the graph G.

Goal: For a given undirected, connected and weighted graph G = (V,E,s,t,l), where l:E->R+, denotes the length function (or weight function), find a spanning tree T in G whose sum of edge weights is minimal.

cost(T) = SUM l(e) for all edges e in T

we call such a tree a minimum spanning tree (MSP).

KRUSKAL'S ALGORITHM
===================

start with subgraph G' contianing only the nodes of G (ie no edges yet).
	while the number of edges in G' is < |V|-1 {
		of all edges in G we have not yet added to G, pick the edge with 
		the smallest weight l(e)
		add edge e to G' unless it creates a cycle in G'
	}

PROOF OF ALGORITHM'S CORRECTNESS
Goal: Show that G' derived by kruskal's algorithm is a minimum spanning tree.

Lemma: Cut property
presume that all edges in G have distinct weights.  Let e be the edge in G with the smallest weight l(e).  Then every MSP of G contains edge e.

Proof: [by contradiction] suppose there is a MST (T) of G which does not contain the edge e' with the smallest weight.  This means that adding edge e' to T would yield a cycle C, ie T would no longer be a tree.
Let edge e be another edge of C that connects a node in S with one in V/S where S is strictly contained in V, S is not the empty set, and S was chosen such that one endpoint of edge e' is in S and the other V/S.

Let T' be the tree we obtain from T by replacing e with e', then:
	T is again a tree as it has |V| = n nodes and |v|-1 edges and as it is connected
	T' is a spanning tree as it contains |v| = n nodes
	cost(T') < cost(T) as l(e') < l(e) because e' is the edge with smallest weight

Then we have that T' would be a MST rather than T, but this is a contradiction with our starting assumption, and so T must contain edge e'.


Theorem: Kruskal's algorithm derives a MST of G.

Observation: The algorithm derives a subgraph without cycles.

(a) let e = (v, w) denote the edge that is about to be added to G' by the algorithm and let S denote the set of nodes to which node v has a path (before edge e is added).
then v in S but w not in S as we would otherwise be creating a cycle in adding e.
As edge e is to be added next, it is the cheapest edge connecting S and V\S.  According to the lemma, we know that edge e belongs to any MST.

Feb 14
======
Feb 14 

Proof of Kruskal's aglorithm's correctness cont.

(b) Let G' denote the sub-graph of G that the algorithm returns, we know that G' does not contain any cycles.

(c) We also know that G' is connected as we would otherwise have a non-empty set S of nodes, S strictly contained in V, with no edges connecting to V\S.  As the input graph G is connected, there is always a connecting edge between any non-empty subset S strictly contained in V and V\S.

(b) & (c) -> G' is a spanning tree of G
(a) -> G' in a minimum spanning tree


Time Complexity of Kruskal's Algorithm (first thoughts)
=======================================================

Reminder of Kruskal's algorithm: start with subgraph of G containing only the nodes of G but no edges
								 while the number of edges in G' is < |V|-1 {
								 	of all edges in G that have no yet been added to G':
								 		select the edge e with minimal l(e) (weight)
								 		add e to G' unless it would create a cycle to do so
								 }


let G have |V| = n nodes, and |E| = m edges

Note the outer while loop is O(n), but we dont yet know the time complexity of the inner steps since the pseudo code is not detailed on the implementation.  So time to introduce a new data structure.


4. AMORTIZED ANALYSIS AND MERGE-FIND DATA STRUCTURE
===================================================

4.1 What is amortized analysis (AA)?
Key idea: express one expensive operation as a finite series of k cheap operations.
		  then show that the worst-case cost (say time cost) for the entire sequence of k operations
		  is lower than the sum of worst-case costs of the k individual operations, ie.
		  	cost( SUM_1 to k (operation) ) <= SUM_1 to k cost(operation)

Definition: Amortized analysis is a set of techniques we can use to get more precise cost-estimates for entire sequences of k operations.

Example: Suppose we are dealing with a series of n calls to operations, each one of:
			PUSH			O(1)
			POP  			O(1)
			MULIPOP(j)		O(n) (since j<=n)

Question: what is hte worst-case time estimate for a series of n operation of the above kind?

Answer: Can push/pop each of the n elements at most once, hence O(n) overall running time.  In particular cannont have n calls to MULTIPOP (at a cost of O(n) each), ie running time must be better than O(n^2)

Conclusion: To get accurate time estimates, need to investivage how the k individual statements influence each other.

4.2 The Potential Method
========================

Key Ideas: we are dealing with a sequence of k individual opertions: op_i with i in { 1,2, ..., k }
we assign to each operation a cost: cost-real(op_i), which corresponds to the actual cost of op_i as well as a cost-am(op_i) called amortized cost of opi whcih constitutes our best guess of the cost of operation op_i (can be <, =, or > the cost-real(op_i)).

when we now execute the sequence of k operations op_i and are currently dealing with operation op_i:
	(a) we pay for / budget for cost-am(op_i)
	(b) if cost-real(op_i) < cost-am(op_i) {
		save 'saved cost' ie cost-am(op_i) - cost-real(op_i) in bank (to spend later if needed)
	} else {
		take cost-real(op_i) - cost-am(op_i) from bank balance IF the current balance allows this
	}

	in the above, interpret
		phi( Di ) = bank balance on total cost of executing operations 1 to i, i in {1, ..., k} where
		Di = data structure after operations 1 to i.
	ie. interpret the bank balance as a function of overall cost of the algorithm up to operation i.

PROPERTIES OF THE POTENTIAL FUNCTION: we impose the following on phi:
(1) phi(Di) >= 0, for all i in {1,...,k}
    ie. we cannot borrow execution time we did not budget for

(2) phi(D0) = 0
(3) phi(Di) = phi(Di-1) + cost-am(op_i) - cost-real(op_i) for i in {1,...,k}

logical flow of argument in the following:
we will start by defining the potential function phi and then determine the amortized costs by enforcing the properties of phi.
we want to show that for a series of n operations 
	SUM_1 to n cost-read(op_i) <= SUM_1 to n cost-am(op_i)
as we can then conclude that the overall running time is <= O( SUM_1 to n cost-am(opi))
(where note that the order of the big-O notation and sum is key)

Example. We have n elements
		 have a mix of k <= n operations PUSH, POP, MULTIPOP(j) where j<= n as before.
		 choose phi(Di) = size of Di <-- data after operation i
		 want (1) phi(Di) >= 0 for all i in { 1,..., k}
		 	  (2) phi(D0) = 0
		 	  (3) phi(Di) = phi(Di-1) + cost-am(op_i) - cost-read(op_i)

IDEA: Choose cost-am(op_i) so (1) to (3) are satisfied
consider op_i = PUSH, statement 3 gives us the constraint that:
	phi(Di) = phi(Di-1) + cost-am(push) - (1)
	phi(Di) - phi(Di-1) + 1 = cost-am(push)
	size(Di) - size(Di-1) + 1 = cost-am(push)
	1 + 1 = 2 = cost-am(push)

using the same strategy for for op_i = POP we find cost-am(POP) = 0.

however MULTIPOP(j) is more complex since we can only pop what has already been pushed:
	constraint 3 <=> cost-am(MULTIPOP(j)) = size(Di) - size(Di-1) + cost-real(MULTIPOP(j))
										  = size(Di) - size(Di-1) + cost-real(MULTIPOP(j))
										  = -j + n


Feb 26
======
Feb 26

4.3 THE UNION-FIND DATA STRUCTURE
=================================

GOAL: Define a data structure which supports the following operations:
	(a) find(x) returns name of set to which element belongs.  so, find(x) =/= find(y) implies that x and y belong to disjoint sets.
	(b) union (A, B): operation takes two sets, A and B, as input and returns their union.
	(c) make Union Find (S): operation takes a set S as input and creates a union-find.

Ideas: For (a) to (c) we could be using a tree like data structure, where every node v corresponds to an element of the corresponding set S, ie v in S, and where every node has a pointer which points to the node after which the set S is named.

ex. S = { i, j, x, y }, pick j as name for the set S.

			j (points to self)
		  ^  ^
		 /    \
		x      y
		^
		 \
		  i

here calling find(x) would return j.

Ideas: (cont) If we are dealing with a set S of size |S| = n, then find(x) for x in S takes at most O(n) as we need to follow at most n pointers.

For each node also remember the size of the corresponding set.
ie at each node in the above tree we would write, "x, n" instead of just x. where n is the size of the set.

ex. A = { v, w, s, y }, v is the name of A, and we also have set B = { u, x, z } name of B is u

		   v,4 (points to self)					u,3 (points to self)
		  ^  ^								   ^ ^
		 /    \								  /   \
		w,?    y,?							 x,?   z,?
		^
		 \
		  s,?

CONVENTION: name union after the larger of the two sets, flip coin if equal.  

			  __________________________________
		   	 /									|
			v									|   
		   v,7 (points to self)					u,3  (now points to the root of the larger set)
		  ^  ^								   ^ ^
		 /    \								  /   \
		w,?    y,?							 x,?   z,?
		^
		 \
		  s,?

Note: we only update the the counter of the root node!  The other's have not been updated yet.
Note: take O(1) time to execute the union since only updating 3->7 at the root node

(c) executing make union find (S) for |S| = n requires O(n) time as we need to create a separate union find structure for every x in S.

ex. S = { x, y, z } would yield:
	x (points to self), y (points to self), z (points to self)
	(I think she means you make n disjoint little trees)

(a) Revisit the time requirement for find(x), GOAL: can we do better than O(n)?
	Hints: realize what union (A, B) does
	consider how often you can make a call to union(A,B) if dealing with n elements only.

	Idea: Realize that the cost of find(x) is:
	- equal to the number of pointers that it takes to reach the node after which the set is named.  
	- This in turn, is equal to the number of times that the set changed it's name 
	- renaming a set however only happens if we at least double it's size, so if the initial size of the set x belongs to is 1, and the final size n, we can have had at most 2^k = n ie k = log(n) doubling's of the set size.  Hence, we have at most log(n) pointers to follow to find the node after which the final set is named.
	Conclusion: find(x) takes only O(log(n)).

Can we do even better?  Consider calling find(x) multiple times for the same x.  After the first execution of find(x), we already know the name of the set containing x.  The same applies to all nodes that we encounter on the path.  If we reset the correspoding pointers to point directly to node x, we can accelerate the future find-commands.  One can show that find(x) can be done in even better time than O(log(n)) <= this is called path compression.

4.4 IMPLEMENTING KRUSKALL'S ALGORITHM USING A UNION-FIND DATA STRUCTURE
=======================================================================

Reminder: start with sub-graph G' containing only the isolated nodes of G. [
		  make union find for set of nodes: O(n)]

		  While the number of edges in G' < |V| - 1:
		  	of all edges that have not yet been added to G', pick the edge e with
		  	lowest cost(e).

		  	add edge e to G' unless it create a cycle in G'.

Suppose G has n nodes and m edges.  
	(1) sorting of edges in G by cost requires O(mlog(m)) time.
		we have at most 1 edge between any 2 nodes (b/c graph undirected) in G, hence, m < n^2
		so we may rewrite the above as O(mlog(n)) time.

	(2) store each of the conneted components of the emerging subgraphh G' in a separate union-find data structure.  when an edge e = (v,w) is considered to be added to G', we execute find(v) and find(w) to check if find(v) = find(w), in which case these two nodes would already belong to the same componenet of G'.  Else, if find(v) =/= find(w) add else e to G', ie execute a corresponding union-command.

	Throughout the algorithm we have:
	at most 2m find operations at a cost of O(log(n)) each as we are adding at most m edges.
	at most n-1 union operations at a cost of O(1) each.
	-> overall the algorithm requires O(mlog(n)) time.



Feb 28
======
Feb 28

Divide and conquer algorithms. 
==============================

Deriving upper bounds for the worst-case running times. 

Divide input into several parts (usually of equal size), solve the problem for each part in a recursive fashion and finally combine partial solutions into one overall solution. 

Use recurrence relation that expresses the running time recursively in terms of running times for smaller instances. 

Example 1: Generic algorithm 
divide input of size n into two parts of n/2 each
solve problem for each part recursively
combine partial solutions into overall solution which requires linear time

Define T(n) = worst case running time of an algorithm for input size n. For the above algorithm, assume that n is a power of 2. 

Then we have T(n) <= c*n + 2T(n/2). 

How many levels k do we need until each subproblem has size 1? Lg(n). 
What is the total size of the problem, i.e. sum of all the subproblems, at each level k? n. 

Just from knowing the mergesort algorithm, we know that the overall running time of this algorithm is nlg(n). Since we need linear time for each “combination”, we can simply take the product of the # of levels k and the total size at each level, and arrive at our final answer. 

To do this more formally for any problem with the recurrence relation T(n) <= q*T(n/2) + cn, we consider the cases where q = 1, q = 2, and q > 2. 

When q = 2, we have 2^k problem instances, and we can solve this just like with mergesort. 

When q > 2, q in N, at each level k we have q^k subproblems, and each subproblem has size n/2^k. Hence, the total work required at level k is c*q^k *(n/2^k), and since we need log2(n) levels, then we have:
T(n) <= q*T(n/2) + c*n <= sum from i = 1 to log2(n) of (q/2)i-1*n*c, which we can simplify to:
T(n) <= c*n(1-(q/2)^(log2(n)))/(1-(q/2))
T(n) <= c*n(q/2)^(log2(n))/(q/2-1)
We can then use:
a^log2(b) = 2^(log2(b)*log2(a)) = b^(log2(a)), so we simplify:
<= c*n(n^log2(q/2))/(q/2-1)
= (c*n*n^(log2(q)-1))  /(q/2-1)
Now, c/(q/2-1) is constant as it does not depend on n [note we have q/2 > 1 as q > 2], so we can then say that this is O(n^(log2(q)))

To summarize: Any function T(n) satisfying the recurrence relation we mentioned previously for q > 2 is upper bounded by O(n^(log2(q))). 

Case 3: q = 1. What changes w.r.t. case 1 and case 2? 
Well, at each level k, we have a single subproblem of size n/2^k. Hence, the total amount of work required at level k is n*c/2^k. Need log2(n) levels to reduce the problem size to 1. 

We can then do a bunch of algebra:
= c*n sum from i = 0 to log2(n)-1 of (1/2)^i, which we can then represent as a geometric sum, which leads to the upper bound, as desired, of c*n*2(1-1/n) <= 2cn  O(n) is an upper bound. 


How about a recurrence relation of the form:
T(n) <= 2*T(n/2) + c*n^2. 
What is the worst case running time O(n)? 
We require c*n^2 /2^k time per level k in total. Hence, our total work can be calculated as:

T(n) <= sum form i = 1 to log2(n) of c*n^2 sum from i = 1 to log2(n) of (1/2)i-1. Which then results in, after a bit of algebra, <= 2cn^2 – 2cn <= 2cn^2 = O(n^2). 

March 5
=======
March 5

COUNTING INVERSIONS
===================
A ranking is a list of n integers, without repeats.

Example: A = (2, 4, 1, 3, 5) B = (1, 2, 3, 4, 5) ie n = 5

Goal: come up wiht a quantitiative way of measuring how similar 2 rankings are.  We want the measure of difference to be zero for two identical rankings.  The measure should increase with a growing number of differences.

Group Work: Propose a measure that compares rankings (ie. a meaningful definition)

Definition: an inversion is a pair of numbers (ai, aj) such that ai > aj and i < j. 
(Ie. she means you label all the numbers by their rankings in one list, ie 
(a1, a2, a3) = (2, 1, 3) -> a1 = 2, a2 = 1, a3 = 3, then if we had another list (2, 3, 1) the number of inversions would be one, the pair 3 and 1 coming in order (3, 1) = (a3, a2))
Example: (2,1) is an inversion as (a1, a3) and 1 < 3.

<< Picture of two rankings, one above the other with lines connecting each element in the above list to it's place in the below list, lines crossing each other indicate inversions). >>

Group Work: Given two rankings A and B of numbers from Wn, what is the maximum number of inversions?

If we are dealing with n numbers from Wn, we have n lines linking each number ai in A to a number bj = ai in B. These lines may have at most:
	n(n-1)/2 = (n, 2) ( ie. Choose(n,2) ) pairwise corssing.  we count every crossing only once, namely the case (ai, aj) with ai > aj and i<j.

We have (n, 2) inversions if A and B are in inverse order, ex A descending and B ascending order.

Note that to check all pairs would require O(n^2) time.

Question: can we actually find an algorithm where worst-case running time is better than O(n^2)?
Idea: 	Cannot look at every possible inversion individually as this might require O(n^2) time.
		use a recursive algorithm
		assume n = 2^k, k integer.

(note that all the following inversions are with respect to some other list B)

(1) Parition A = (a1, ..., an ) into two lists of n/2 length each.  
		A1 = (a_1, ..., a_n/2) and A = (a_n/2+1, ..., a_n)
(2) (recursively) Count the number of inversions in A1 and A2 separately
(3) Count the number of inversions where one number belongs to A1 and another to A2.
	[ this corresponds to the step where we combine two partial solutions into one, ie. we still need to determine how efficiently we can do this]


-> We are dealing with a binary tree (because of (1)) with log(n) levels, but it is yet unclear how efficiently we can combine partial solutions into one.

-> Have a recurrence relation: T(n) <= 2*T(n/2) + ???

Goal: Find out how to combine partial solutions efficiently.  
	have: 2 sorted lists A1 A2, for which we know the number of inversions.
	(call A = A1 and B = A2 in the following:)
	want: a single sorted list A' while counting the inversions between A and B.

Recall the merge sort algorithm
Question: Can we modify the merge sort algorithm to count inversions between A and B while producing A'?
We need to count the number of pairs (a,b) with a from A, and b from B, and a > b (ie an inversion).

Yes, rough algorithm: 
if ai < bj, we move ai to list A' and we know that we are NOT dealing with an inverison as everything left in list B beyond bj is also larger ai.
else ai > bj we move bj to A' as we know that bj is smaller than all elements in A as this list is already sorted. Thus, when ai > bj we know  (without explicitely counting) that we have |A| inversions, where |A| is the number of elements in A at this time.

our new algorithm is:
Merge-and-count(A,B) :
	keep a separate pointer for A and B which point to the first element to start with
	set count = 0 which is equal to the number of inversions encountered
	while both lists A and B are not empty {

		let ai and bj be the elements being pointed to
		append min(ai, bj) to new combined list C
		if ( ai > bj ) {
			count += remaining number of elements in A
		}
		advance the pinter corresponding to min(ai, bj)
	}

append rest of list which has not been completely emptied onto C
return count and list C

Definition: Sort-and-Count(A)
	let n denote the length of A
	if (n=1) { enter 0 as number of inversion and A itself as list }
	else {
		divide A into two smaller lists A1 and A2 of roughly equal size
		A1 contains first ciel(n/2) elements of A
		A2 contains the remaining elements of A
		(rA, A1) = sort-and-count(A1)
		(rB, A1) = sort-and-count(A2)
		(r, L) = merge-and-count(A1, A2)
		return (r + rA + rB) as the number of inversions and list L
	}

Conclusion We are dealing with an algorithm of the following recurrence relation:
	T(n) <= 2*T(n/2) + c*n
	-> (from 5.1) the algorithm requires O(nlogn) time.



5.2.2 Example 2: Finding the closest pair of points in two dimensions
=====================================================================

Reminder: for n points in R^2 we need to calculate (n,2) distances to find the answer, ie. which requires O(n^2) time.
Goal: can we do better?

Consider the 1 dimeionsal case: n points in R.  
Strategy: first, sort all points according to their x-coordinates (this requires O(nlogn) time), then we walk through the sorted list and caluclate distances between adj pairs of points (O(n) time) and keep track of the minimum distance found.  Overall the algorithm is O(nlogn) to solve the 1 dimensional problem.

2 dimensional case:  we will try to recycle some ideas fromt the 1 dimensional case.
every one of the n points may be denoted as a vector (x y) in R^2 (not to be confused with choose notation (n, m) <- comma).  
define the distance d(p1, p2) = sqrt((x1-x2)^2 + (y1-y2)^2).
We will additionally assume all points p in our set have distinct x and y coordinates.

key 1. use a divide and conquer approach: 
	(1) divide the set P of n points into two halves (P1, P2), based on their x-coordinates (this requires O(nlog(n) time, see the one dimensional case).
	Sort all n points in P according to their:
		x coordinate -> list Px
		y coordiante -> list Py
	We remember in the follow for each point p in P what its position is in Px and Py.

... To be continued next class.





March 7
=======
March 7

5.2.2 (cont)
============

Idea 2: (cont) given n points of set P, i.e. p = (x y) in R^2
(1) divide P into two halves P1, P2, separting points by their x coordinate (this sorting takes O(nlogn) time)

	Px = a sequence of the points in P sorted with respect to their x coordinate
	Py = a sequence of the points in P sorted with respect to their y coordinate
	Rememeber, for each point p in P, its rank in each of the above lists.

(2) For P1 and P2 (recursively) identify the closest pair of points in each:
	(p1_0, p1_1) = closest pair of points in P1
	(p2_0, p2_1) = closest pair of points in P2

	Compile lists P1x and P1y and likewise P2x and P2y which are the x and y sorted sequences of points from P1 and P2.
	This requires O(n) time as we jsut have to extract entries from Px and Py respectively.

(3) Merging Solutions:
	We know the closest pair of points in P1 with distance = d(p1_0, p1_1) and likewise the same for P2 with distance = d(p2_0, p2_1) but we have not yet considered any pairs where one points is from P1 and the other from P2.

	delta = min( d(p1_0, p1_1), d(p2_0, p2_1) ) = the minimum value found so far, not yet considering pairs spanning the two sets

	Question: is there a pair of points p1 in P1 and p2 in P2 such that d(p1, p2) < delta.

	Group work: how would you go about this?
		my answer: check all pairs across the boundary with x-distance < the distance delta
		laszy upper bound: check all points x to the left of the line, and x to the right.

	(a) The above is what we ended up doing, maths:
		If the distance d(p1', d2') < delta then p1' have to lie within delta of the dividing line.
		Pf: let x' be the x-coordinate of the dividing line, p1' = (p1'x, p1'y) p2' = (p2'x, p2'y), then:
			p2'x - x' <= p2'x - p1'x <= sqrt( (p2'x - p1'x)^2 + (p2'y - p1'y)^2 ) = d(p1', p2') < delta
			p1'x - x' <= p1'x - p2'x <= sqrt( (p2'x - p1'x)^2 + (p2'y - p1'y)^2 ) = d(p1', p2') < delta
			
	(b) any two points in P1 (and likewise any 2 in P2) are at least a distance delta apart (else delta is the shortest distance between any pair within either P1 or P2).

	Draw a grid of delta/2 widht/ height in the 'interesting area' (the region delta away from the dividing line).  Then every box of that grid contains at most 1 point (this because any two points within the same box would have a distance <= delta/sqrt(2) < delta).

	(c) given one particular point p1' in P from the interesting area, how many boxes do we need to consider to find a potentially interesting p2' in P2?
	Turns out we need only consider up to 10 boxes, ie since there is at most 1 point in each box this means we only need to consider up to 10 possible pairs.

	(a), (b), (c) conclusion -> in order to check for a possible interesting pair (p1', p2') with d(p1', p2') < delta we:
	loop over the y sorted list of points in P1 that are x-coordinate-wise at most delta away from the dividing line.  
	For any such p1' compute the distance to at most 10 other points p2' in the y-sorted list P2.
	If we find an interesting pair d(p1', p2') < delta we keep track of their minimum distance and report it once we are finished looping over elements in P1.
	Worst case (all points of P1 in the interesting area) we have to do this for |P1| = n/2 points, ie the step is O(n).

	Big conclusion: We are dealing with a divide and conquer algorithm whose recurrence relation is:
		T(n) <= 2*T(n/2) + cn
		ie. we know that its worst case running time is O(nlog(n)) (note this beats the O(n^2) straight forward brute force algorithm).

	Reference: Pseudo-code, see p.230 (section 5.4) in the text book (but this would not appear on the text).


6. RANDOMIZED ALGORITHMS
========================

Key idea: modify some divide and conquer algorithms to reduce their expected worst case running time.

Implementation: Algorithms use one (or more) non-deterministic steps, ie. we need to consider expectation values for random variables.

Typically, we will construct a non-deterministic ways to divide a given problem into several sub-problems (divide step)

6.1 example 1) finding the median
=================================

Goal: Given a set of numbers S, |S| = n, S = {a1, ..., an}, find its median value.
Assume: n numbers in S are distinct.
Definition: The median value of such a set S is equal to the kth largest element in S, where:

	k = {	(n+1)/2 if n odd
			(n)/2 if n even

We know we can fin the median by first sorting the set in O(nlogn) time and then picking the kth largest element from the sorted list.

Goal: find a randomized algorithm which has an expected worst-case running time better than O(nlogn) 

Idea 1: Think about a slightly more general algorithm, called Select( S, k ) that takes as input a set S of n numbers and returns the kth largest number (where k in {1, ..., n}).
So, determining the median for S amounts to select( S, k ) 

Strategy behind select(S,k)
	(1)	Choose an element ai in S (the splitter)
	(2) form sets:
		S- = {aj in S, s.t. aj < ai}
		S+ = {aj in S, s.t. aj > ai}
	(3) Determine if S- or S+ contains the desired k-kth largest element in S and only continue with that set (in the recursion).

We need to decide how to choose the splitter, the overall goal is to get a worst case running time of O(n).

March 12
========
6.1 (cont) Finding the Median

Goal: Do better than O(nlogn) 

Stragtegy: Devise an algorithm called select(S,k) where |S| = n and k in {1,...,n} to find the kth largest element in S.

The algorithm:
Select(S,k):
	choose splitter ai
	for each aj in S:
		if (aj < ai): 
			move aj to S-
		else if (aj > ai)
			move aj to S+

	if |S-| = k-1:
		ai is the desired kth element
	else if |S-| >= k:
		call Select(S-,k)
	else:
		call Select(S+, k-(l+1))			(where l = |S-|)

Group work: 
What does Select(S,1) retrieve?
What about Select(S,n)?
Why do we call Select(S, k-(l+1)) in the else clause?

Asking for the k-th largest element in S is qual toasking for the k-(l+1)th element in S+ as we know n the else clause that |S-| = l and |S- union {ai}| = l+1 and S- union {ai} does not contain the kth largest element.

Observations:
- the algorithm terminates as it makes recursive calls to strictly smaller sub-sets.
- If we chose the splitter element wisely, we reduce the original problem size by 50% at each iteration.  We would get a recurive relation:
	T(n) <= 1 * T(n/2) + c * n, c in R

This fits generic alg. No 1, hence O(n) time requirement.

Idea 2. In the Select(S,k) alg. we choose the splitter a, uniformly at random from S.  Using this idea, every element in S has the same probability of being selected.

Definition: Given a set S of n distinct elements, S = {a1, ..., an}.  We call an element ai in S central if: at least one quarter of the elements in S are smaller than ai, and likewie at least a quarter of the elements in S are larger than ai.

Implications: As the Select algorithm is no longer deterministic, we can from now on only talk about expected running times.

Definitions: 

We will say the algorithm is in phase j if the problem size a we are dealing with is n(3/4)^(j+1) < z <= n(3/4)^(j).  (we expect the problem size to shrink by a factor of 3/4 or more at every iteration if we can expect the splitter to be central)

Let X be a random variable that is equal to the number of recursions of the algorithm, ie.
X = X0 + X1 + X2 + ... 
where Xi denotes the expected number of steps that the alg spends in phase i.

Observations:
(1) at any phase j, the probability of choosing a central element splitter is 1/2.  So expect to have to make 2 iterations before the randomly chosen splitter will be central.
(2) When the alg is in phase j, the problem size is at most n(3/4)^j. So we require at most c*n(4/3)^j steps (at every iteration?) in phase j for some constant c in R.

(1)&(2) -> the expected number of steps of the alg. in phase j is:
	E[Xj] <= 2*c*n(3/4)^j  where E is the expectation for Xj

The expected total number of steps of the alg is (Sum over the phases):
	E[X] = SUM_j=0 to m ( E[Xj] ) <= SUM_j=0 to m ( 2*c*n(3/4)^j ) = 2*c*n SUM_j=0 to m ((3/4)^j)
	<= 2*c*n SUM_j=0 to inf ((3/4)^j) = 8*c*n.

Conclusion: The expected running time of Select(S,k) is O(n) for |s|=n.


6.2 Example: Sorting numbers
Goal: Given a set S of distinct natural numbers, sort them.
Devise a divide and conquer algorithm to solve the problem.

Idea: Use same idea as in previous example, ie. divide input S according to a splitter into two susets, but kee considering both subsets rather than discarding one.  Once again we will choose the splitter in a uniformly random way from S.

QuickSort(S):
if |S|<=3:
	Sort S and return answers
else:
	while no central splitter has been selected:
		chose splitter ai in S uniformly at random.
		for each element aj in S:
			if (aj < ai):	
				move aj to S-
			else:
				move aj to S+
		if (|S-|>= |S|/4 and |S+|>= |S|/4):
			// ai is a central splitter so we break while loop

	call QuickSort(S-)
	call QuickSort(S+)
	return (sorted list S-, ai, sorted list S+)

Observations:
It takes O(|S|) = O(n) time to check if a splitter is central when dealig with set S.
Because we expect to pick a central splitter after 2 iterations of the while-loop, the alg requires O(|S|) time, excluding time spend on recursive calls (ie. this is just time spent at the first step).

Definition: We wil call a sub-problem of the alg to be of type j if the size z of the sub-problem is n(3/4)^j+1 < z <= n(3/4)^j.

Observation 1: The expected time spend on a sub-problem of type j (excluding the recursive calls) is O(n(3/4)^j).

Observation 2: Splitting a sub-problem of type j using a central splitter creates two disjoint subproblems of type j+1.

Question: What is the total number of subproblems of type j that we may encounter?  Call this quantity X.

Answer: (a) we have a problem of size n to start with.
		(b) we know that the minimum size of a any problem of type j is n(3/4)^j+1 
		(c) we know that this total probkem size remains n for different values of j.

(a), (b) & (c) -> n = X*n*(3/4)^j+1 <-> X = (4/3)^j+1

Question: what is the expected amount of time required to sort out all subproblems of type j?

Answer: we already know that we:
	have at most (4/3)^j+1 subproblems of type j
	each sub-problem has a size of at most n(3/4)^j
	the expected running time of the alg (excluding recursive calls) is linear in the set-size
	-> for each subproblem of type j, require O(n(3/4)^j) expected time
	so overall, for all subproblems of type j, require O((4/3)^j+1 * n * (3/4)^j) = O(4/3 * n) = O(n) time.

	AS the overall problem remains n for all types j, require a total of O(log(n)) types.

Conclusion: QuickSort(S) has O(nlogn) exp running time.

March 14
========
7. DYNAMIC PROGRAMMING - not on midterm
=======================================

Key ideas:
	we want to identify a globally optimal solution.  For this, we need to define what we mean by best solution.  Express the overall state that any solution can be assigned as a sum or product of states for the partial solutions.

	Search the space of all possible solutions in an efficient manner by looking at:
		successively at larger solutions
		by discarding sub-optimal solutions to sub-problems as early as possible

7.1 Ex. Weighted inverval matching
Setting: given a set S of n weighted intervals:
	S = { (s(1), f(1), w(1)), ..., (s(n), f(n), w(n)) } where s(i) < f(i) in pos reals
														and w(i) is the weight of interval i

Task: Find an optimal sub-set T of S such that
	- the intervals in T are mutually non-overlapping
	- there is no subset T' of S whose intervals are also non-overlapping and whose sum of interval weights is larger.

The weight w(i) of interrval ihas nothing to do with its length.
Assume: intervals in S are sorted according to their endpoints, ie f(i) <= f(j) for i<j

Def: Sj = {(s(i), f(i), w(i)) s.t i <= j }
ie subsets of intervals from S with endpoints f(i) <= f(j)
W(j) = the sum of wieghts for the best interval scheduling for set Sj
C(j) = largest Set of i < j such that intervals i and j do not overlap, c(j) = 0 if no such interval exists.

Algorithm: Weighted Interval Scheduling (S)
W(0) = 0
for (i = 1 to n ):
	W(i) = max( W(i-1), w(i) + W(c(i)))  
	- note weight stays the same, we are not including the weight of interval i 
	- W(c(i)) is the optimal solution to and excluding interval i and adding the weightof i becasue we knwo that intervals c(i) and i are mutually compatible.

	T = empty
	last_i = n
	while (last_i > 0):
		if w(last_i) > w(last_i=1):
			add last_i to set T
			last_i = c(last_i)
		else:
			last_i = last_i-1

return T


Deriving an alternative algorith that does not require c(j) - values

Definitions:
S and Sj as before n = |S|
New: W(j) = the sum of weights of the last interval scheduling for Sj that ends in and includes interval j itself.
t(i,j) = { 1 if i and j are compatible, 0 else }
Wi^0 = W_i union {0}
Start and end are fake intervals of weight 0 that are compatible with all intervals in S

Alg: Weighted interval scheduling
=================================
initializiation: W(0) = 0 <--- start interval

recursion:
	for i = 1 to n:
		W(i) = max{ W(j) t(j,i) } + w(i) max over j in { 0,..., i-1}

termination: W(n+1) = max{ W(j) t(j, n+1)} + w(n+1) max over j in {0,..., n}
				end interval		= 1			= 0

traceback: 
	T = empty
	last_i = argmax{ W(j) t(j, n+1)} + w(n+1) max over j in {0,..., n}

	while (last_i > 0):
		add last_i to T
		last_i = argmax{ w(j) t(j, last_i) } over j in {0,..., i-1}
	return T
			



March 21
========
March 21

Weighted JS (version 2)
w(0) = 0
for (i=1, ..., n){
	w(i) = max{ w(j)t(j,i) } <-- where t(j,i) is 1 if ij are compatable, else 0
			 j in {0,...,i-1}
}
w(n+1) = max { w(j)t(j, n+1) }
			j in {0,...,n}

Theorem: The algorithm (v2) returns the optimal solution.
Proof: (the strategy is proof by induction)
We first show that w(i) corresponds to the weight of the best path up to and including interval i.  This directly implies that w(n+1) is the weight of the overall best solution.  We then show that the traceback procedure recovers the underlying set of intervals.

(1) Proof by induction:
j=0, w(0) = 0 is the weight of the best path starting at interval 0 and ending at interval 0 (which has a weight of 0).

Suppose that w(i) corresponds to the weight of the best path up to and including interval i.  When we calculate w(i+1) via:
	w(i+1) = max{ w(j)t(j,i+1) } + v(i+1)
				j in {0,...,i}
	we know that the max operation will select the interval j in {0,...,i} that:
		is compatable with interval i+1, ie t(j, i+1) = 1
		and has the highest value w(j)

we already know that the weights w(0) to w(i) correspond to the weight of the best path up to that respective interval.
By adding the weight of the current interval, v(i+1), we therefore obtain the weight of the best path from interval 0 to (i+1).  
Note: for i=n, we do not need to add weight v(n+1), as it is 0.



Weighted JS (version 2) - traceback only
T = {}
last_i = argmax{ w(j)t(j, n+1) }
			j in {0...n}
while ( last_i > 0){
	add last_i to set T
	last_i = argmax{ w(j)t(j, last_i)}
				j in {0...lasti-1}
}
return T

(2) We know that w(n+1) corresponds to the weight of the optimal path.  In order to retrieve the corresponding path, we start at interval n+1 (END interval) and proceed via intervals that were selected in the max-operation of the for loop. until we reach the start interval 0.
w(n+1) arrives from the interval j in {0...n} that maximizes w(j)t(j,n+1).  This is equal to the first value of last_i (*).  When we are at interval last_i, we know that the previous interval j is the interval j in {0,...,lasti-1} that maximizes w(j)t(j,last_i).
We  therefore set the new value of last_i to argmax{ w(i)t(j,last_i)}, add last_i to return set T and continue until we reach the START interval 0.

7.2 Example 2 Segmented Least-Square Problem
============================================

Problem Setting: Given a set S of n points in 2 dimensions, determine the linear fit to these points that minimizes the overal distance to all n points.

Definitions: S = {p1, p2, ..., pn}, where the points pi = (xi, yi) have indicies such that x1 < x2 < ... < xn. where |S| = n.

a line in 2d is defined via a function l(x) = y = ax + b.  We call a the slope of the line and b the intersection wiht the y axis.

the distance between a line l and a set of points S is defined as:
	e(l,s) = SUM_1 to n ( y-l(x) )^2 = SUM_1 to n ( yi - (axi + b ))^2 = SUM_1 to n (yi - axi - b)^2 

Goal: Given a set S, |S| = n , find values a and b in R such that e(l,S) is minimized for the corresponding line l defined by a and b.

Solution (calculus) Interpret e(l,s) as function g(a,b) (as s is kept fixed)
Set the partial derivatives wrt to a and b = 0 and use the resulting to equations to derive a and b.

... maths skipped ...


a = n SUM_1 to n (xiyi - (SUM_1 to n xi)(SUM_1 to n yi))/(n* SUM_1 to n xi^2 - (SUM_1 to n xi)^2)

b = (SUM_1 to n yi - a SUM_1 to n xi) n

-> these valeus define the correspoding line unambigugously, this is the line that minimizes e(l,s).

Definitions: a partition of P into N segments is a decomposition of set P = {p1, ..., pn} (with x1< x2 <... <xn as before) into N sub-segments S_i i in {0...N} such that:
	UNION Si = P, Si =/= {}, Si INTERSECT Sj = {} for any i =/= j
	and Si = {P_s(1), ..., P_e(1)} with s(i) <= e(i)

	and where e(i-1) + 1 = s(i) and e(i) + 1 = s(i+1)

	Example. P = {p1, ..., p_15}
	get parition:
		S_1 = {p1, p2, p3} s(1) = 1, e(1) = 3
		S_2 = {p4, p5}	   s(2) = 4, e(2) = 5
		S_3 = {p6,...,p15} s(3) = 6, e(3) = 15


	e_ij = minimal error e(l,s) for the optimal line l(x) through points {pi,...,pj} i<j

	Definitions P(S1,...,SN) the penalty for a given partition of P into segments S1,..., SN
		= SUM_1...N ( e_s(1)e(1) + c)  where c in R is the penalty per segment

	Goal: Given a set P of n points, find the optimal partition into segments that maximizes the overall penalty defined above, keep chosen value of C fixed.

	key observations:
		Suppose M(i) corresponds to the minimum penalty up to and including pi.  Suppose we know the values of M(1) to M(i-1).  

		M(i) = min{ M(j-1) + e_ij + c }
				j in {0...i}

	Segmented least squares algorithm (P,n)
	- calculate a nxn maxtrix E:
		for (i=0...n) {
			for (j=0...i) {
				calculate eji
			}
		}

		eji is the minimum penalty fit for a single line to points pj,...,pi

M[0] = 0
for (i=0...n){ M[i] = min {M[j-1]+eji+c} }

traceback T = {}
last_i = argmin{ M[j-1] + ejn + c }  segment p_lasti to pn
			j in {0...n}

while ( lasti > 0){
	move lasti to T
	lasti = argmin{ M[j-1]+ejlasti-1 + c }    segment p lasti to lasti-1)
				j in {0...lasti-1}

return T and |T| = N (ie boundry indicies of all segments and their number)

Observations: M[n] contains overall penalty

Time requirements:
	calculate E-maxtrix, n^2 values eji each of which require O(n) time to calculate
	-> O(n^3) time

	recursion O(n^2)
	traceback O(n^2)
	overall the algorithm is O(n^3) time.

March 26
========
March 26 

7.3 Sequence Alignment
======================

Motivation: We want to compare a given pair of strings.
Ex. Two strings X = STOP and Y = TOPS, we may want to align them:
	STOP-
	-TOPS  <--- where the dashes are 'gap' characters, where one string is lacking a char but not the other

We need a quantitative score to judge the quality of a potential alignment given two input strings.  Need a clear procedure (algorithm) to optimize the overall score so we can identify the best alignment give two input strings.

Key idea: judge any possible alignment based on:
	(a) the number of gaps
	(b) the number of mis-matches

Definition: a mismatch is an alignment of two characters p and q where p =/= q.

Definition: given sequences X = (x1, x2, ..., xl_x) (of length l_x)
							Y = (y1, y2, ..., yl_y) (of length l_y)
			a global alignment, A, between two sequences X and Y is a pair of strings X' and Y' of the same length l_A (the alignment length), where X' in Ax union { - } and Y' in Ay union { - } (where Ax and Ay denote the alphabets from which the symbols in X and Y derive) s.t.:
							if we remove the gap chars from X' we obtain X
							if we remove the gap chars from Y' we obtain Y
							two gaps are never aligned, ie. there is no i {1...l_A} with x'_i = y'_i = '-'.

delta in R+ is the gap penalty.
alpha_pq is the mismatch cost of aligning p to q.  Usually, alpha_pq = 0 iff p == q, else alpha_pq > 0.
the cost of alignment A between sequences X and Y is:
	c(A, C, Y) = SUM_i to l_A ( ci ) 	where ci denotes the cost/penalty for alignment of column i

	For our example c(A,X,Y) = delta + alpha_tt + alpha_oo + alpha_pp + delta

GOAL: Given X and Y and chosen penalties delta and alpha_pq, find the optimal alignment A* = argmin{c(A,X,Y)}.

BIG QUESTION: given X and Y how many possible alignments are there?

Smaller question:  What is the min is the middle of the maximum length of any aligment A between X and Y?
Lmin = max{lx, ly}
Lmax = lx + ly

question 2: Given a fixed alignment length lA in {lmin,...,lmax} what is the number of different alignments of that length?
gapsx = lA - lx, gapsy = lA - ly (note the () in the following are choose notation)
-> the number of different possible configurations of X' = ( lA gapsx ) = ( lA lA-lx ) = the number of ways of inserting gapsx indistinguishable gaps in lA position.
-> for a fixed configuration of X' the number of configurations of Y' = ( lA - gapsx gapsy ) = ( lx lA - ly )
so in total we have that there are ( lA lA-lx )*( lx lA-ly ) alignments for a given aligmnent length lA.

BIG QUESTION FINALLY:
Then summing over the total alignment length we have that there are a total number of alignments of:
N(lmin, lmax) = SUM_lA = lmin to lA = lmax ( lA lA-lx )*( lx lA-ly )

Ex. N(L,L) ~= (1+sqrt(2))^(2L+1) / sqrt(L)

So we don't want to brute force this, is the point of that.

Definitions: M(i,j) = the minimal cost of an alignment between sub-sequences Xi = (x1...xi) and Yj = (y1...yj)
					= the cost of an optimal alignment between Xi and Yj

Key Observation: if we happen to know the values of M(i,j-1) M(i-1,j-1) and M(i-1,j) then we can derive M(i,j) as follows:
		M(i,j) = min( M(i-1,j-1) + alpha_xiyj,    align xi, yi
					  M(i-1,j) + delta,			  align xi to a gap
					  M(i,j-1) + delta)			  align yj to a gap

Why dont we consider, when calculating M(i,j), 
					say M(i-1,j) + alpha_xiyj ?
					M(i-1,j-1) + delta 		  ?
					M(i,j-1) + alpha_xiyi     ?

my answer: going from M(i-1,j) to M(i,j) you would never be aligning xi to yi, same to all, so these questions are silly.

Optimal Alignment( X, Y ):
	
	allocate 2d-matrix M of (L_x + 1) x (L_y + 1) elements
	M[0,0] = 0
	for i = 1 to lx:
		M[i,0] = i * delta
	for j = 1 to ly:
		M[0,j] = j * delta

	for i = 1 to ly:
		for j = 1 to lx:
			M[i,j] = min{ M(i-1,j-1)+alpha_xiyj, M(i-1,j) + delta, M(i,j-1) + delta }

	return M[lx,ly]

-> to retrieve the corresponding alignment we could have been assigning pointers as we went through the 2d array, so that each square knows which square it took its minimum value.

Time requirements: O(lx*ly)










March 28
========
March 28

8. NP-completeness 
==================

So far: Have considered a range of problems that can be solved efficiently, ie. where algorithms exist that run in polynomial time to solve the problem.

Motivation: If we do not happen to know an efficient alg for sorting a given problem, this does not imply that such an algorithm does not exist.

Question: Can we come up with a meaningful way to categorize difficult problems according to their difficulty?

Answer: YES (to some extent)

Definition: We can define the class of NP-complete problems as the set of those difficult problems for which:
	- no polynomial time algorithm is know to solve any of them
	- but which are of similar difficulty in the sense that if we know an efficient algorithm to solve one of the problems then tis would allow us to devise efficient algorithms to solve all the problems.

8.1 Polynomial time reductions
==============================
Goal: We want to rank comparitively difficult problems via pairwise comparisons (eg. problem X is as least as difficult to solve as problem Y)

Definition: Given two problems X and Y, we say that Y is polynomial time reducible to problem X (write Y <=p X) if arbitrary instances of Y can be reduced using:
	- a polynomial number of standard computational steps
	- a polynomial number of calls to the algorithm that solves X.  We then say, X is at least as hard to solve as problem Y with respect to polynomial time.

Theorem 1: given 2 problems X and Y with Y <=p X, if X can be solved in polynomial time then Y can also be solved in polynomial time.

Proof: Because of Y <=p X any instance of Y can be solved by a polynomial number of default computational steps plus a polynomial number of calls to an efficient (ie. polynomial time) algorithm to solve X.  Hence we can solve Y in polynomail time.

Theorem 2: Given two problems X and Y with Y <=p X.  If Y cannot be solved in polynomial tiem, then X cannot be solved in polynomial time.

Proof: Theorem 2 is the contrapositive of theorem 1.  ie. the two statements are equivalent.

Example 1: Independent set and vertex cover
===========================================

Problem 1 (indep. set): Given an undirected graph G and a initial number k in N, does G contain an indep. set of size k or larger?

Definition: Given an undirected graph G = (V,E).  We call a set S of indicies, S contained in V, independent if there is no pair of nodes in S that are connected by an edge.

From 2.6.4, we know that the brute force approach of finding an indep. set of size k for a graph G with n nodes requires us to look at choose(n, k) subsets of size k.  This takes O(n^k) time.

Problem 2 (vertex cover): Given an undirected graph G =(V,E) and a number k in N does G contain a vertex cover of size <= k?

Definition: given G as above, A subset of nodes S in V is a vertex cover if every edge e of E has at least one of it's nodes in S.

Strategy: In order to show that the two problems are of comparable difficulty, we will show that
	- (P1) <=p (P2)
	- (P2) <=p (P1)

Theorem: Given an undirected graph G=(V,E) and a subset S of V, then the following equivalence holds:
	S is independent <==> V\S is a vertex cover

Proof: 
-> Suppose S is an independent set for G.  Consider an arbitrary edge e = (u,v) in G.  As the set S is indep we cannot have that both u and v are in the set S.  This imples that either u or v are in V\S (or both).  As edge e was arbitrarily chosen we can then conclude that V\S is a vertex cover.

<- Suppose V\S is a vertex cover, ie. every edge in E has at least one of its nodes in V\S.  That is every edge does not have both nodes in S.  So consider any two nodes (u,v) in S. If G contained some edge e = (u,v) and neither node u,v were in V\S then V\S could not be a vertex cover (a contradiction).  It then follows that any two nodes in S are not connected by an edge and that S in an indep. set.

lemma 1: (Indep. set) <=p (vertex cover)
Proof: This follows immediately fromthe previous theorem and the defintion of <=p.  This is because any instance of the indep set problem can be solved by using an alg to solve the vertex cover problem (for the same graph G).

The previous theorem allows us to convert V\S into the desired set S which solves the intep set problem.

Lemma 2: (vertex cover) <=p (indep set)
Proof: Strictly analogous to the proof of lemma 1.


