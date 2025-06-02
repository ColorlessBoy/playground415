Consider a polynomial $P(x)=\left(x+d_{1}\right)\left(x+d_{2}\right) \cdot \ldots \cdot\left(x+d_{9}\right)$, where $d_{1}, d_{2}, \ldots, d_{9}$ are nine distinct integers. Prove that there exists an integer $N$ such that for all integers $x \geq N$ the number $P(x)$ is divisible by a prime number greater than 20 .

Note that the statement of the problem is invariant under translations of $x$; hence without loss of generality we may suppose that the numbers $d_{1}, d_{2}, \ldots, d_{9}$ are positive. The key observation is that there are only eight primes below 20, while $P(x)$ involves more than eight factors. We shall prove that $N=d^{8}$ satisfies the desired property, where $d=\max \left\{d_{1}, d_{2}, \ldots, d_{9}\right\}$. Suppose for the sake of contradiction that there is some integer $x \geq N$ such that $P(x)$ is composed of primes below 20 only. Then for every index $i \in\{1,2, \ldots, 9\}$ the number $x+d_{i}$ can be expressed as product of powers of the first 8 primes. Since $x+d_{i} > x \geq d^{8}$ there is some prime power $f_{i} > d$ that divides $x+d_{i}$. Invoking the pigeonhole principle we see that there are two distinct indices $i$ and $j$ such that $f_{i}$ and $f_{j}$ are powers of the same prime number. For reasons of symmetry, we may suppose that $f_{i} \leq f_{j}$. Now both of the numbers $x+d_{i}$ and $x+d_{j}$ are divisible by $f_{i}$ and hence so is their difference $d_{i}-d_{j}$. But as $$ 0 < \left|d_{i}-d_{j}\right| \leq \max \left(d_{i}, d_{j}\right) \leq d < f_{i} $$ this is impossible. Thereby the problem is solved.

考虑一个多项式
$P(x) = (x + d_1)(x + d_2) \cdots (x + d_9)$,
其中 $d_1, d_2, \ldots, d_9$ 是九个互不相同的整数。证明存在一个整数 $N$，使得对于所有满足 $x \geq N$ 的整数 $x$，数 $P(x)$ 必然能被一个大于 $20$ 的质数整除。


注意该问题陈述在对变量 $x$ 进行平移时不变，因此不失一般性，我们可以假设所有的 $d_1, d_2, \ldots, d_9$ 都是正整数。关键观察点是小于 20 的质数只有八个，而 $P(x)$ 涉及的因子超过八个。我们将证明当
$N = d^{8}, \quad \text{其中} \quad d = \max\{d_1, d_2, \ldots, d_9\}$
时， $N$ 满足题目所需的性质。

假设反设存在某个整数 $x \geq N$，使得 $P(x)$ 仅由小于 20 的质数构成。则对于每个索引 $i \in \{1, 2, \ldots, 9\}$，数 $x + d_i$ 可以写成前八个质数的幂的乘积。由于
$x + d_i > x \geq d^{8}$,
存在某个质数幂 $f_i > d$ 整除 $x + d_i$。

根据鸽巢原理，必定存在两个不同的索引 $i \neq j$，使得 $f_i$ 和 $f_j$ 是同一个质数的不同幂。考虑对称性，不妨设
$f_i \leq f_j$.

那么， $x + d_i$ 和 $x + d_j$ 都能被 $f_i$ 整除，因此它们的差
$d_i - d_j$
也能被 $f_i$ 整除。

但由于
$0 < |d_i - d_j| \leq \max(d_i, d_j) \leq d < f_i$,
这显然不可能。

因此，假设不成立，题目得证。
