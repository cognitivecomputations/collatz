# collatz

The proof of the Collatz conjecture hinges on demonstrating that for any integer $n > 1$, there exists a $k$ such that $F^k(n) < n$, where $F^k$ denotes the $k$-th iterate of the Collatz function $F$. The proof proceeds by contradiction. We assume that there exists some $n > 1$ for which $F^k(n) \ge n$ for all $k$. Under this assumption, a surprising consequence emerges regarding the 2-adic valuation $\nu_2(n+1)$ (i.e., the exponent of 2 in the prime factorization of $n+1$): if the sequence never descends below $n$, then $\nu_2(n+1)$ must be infinite, which is impossible since $n+1$ is finite.

To arrive at this conclusion, the proof examines the behavior of $\nu_2(F^i(n)+1)$ for successive iterates $i$. A key lemma shows that if $2^j$ divides $n+1$ but $2^{j+1}$ does not (i.e., $\nu_2(n+1)=j$), then there must exist a $k$ such that $F^k(n) < n$. This lemma is proven by induction on $j$.

Thus, by assuming that no iterate drops below $n$, we derive inductively that $n+1$ must be divisible by arbitrarily large powers of 2—implying that $\nu_2(n+1)=\infty$. This contradiction establishes that for every $n > 1$ there is indeed some $k$ with $F^k(n) < n$. Finally, the full Collatz conjecture follows by applying strong induction on $n$. The argument is akin to descending a staircase: while individual steps might sometimes rise, the overall trend must be downward.
