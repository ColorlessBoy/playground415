# Question. 

(1997, 38th IMO) Find all pairs of integers $(a, b)$, where $a \geqslant 1, b \geqslant 1$, that satisfy the equation $a^{b^{2}}=b^{a}$.

# Answer. 

- 若 $a=1$, 则由 等式得 $b=1$，此时解为 $(1,1)$.
- 若 $a \ge 2$
  - 设 $b=1$, 则由题中等式得 $a^{b^{2}}=b^{a}=1$, 与 $a \ge 2$ 矛盾。
  - 接下来需要解决的情况是 $a \ge 2$ 和 $b \ge 2$。

> **新增条件 $a \ge 2, b \ge 2$**

首先，根据有理数的最简分数表示定理，我们可以将 $a$ 和 $b$ 表示为最简分数。
$\exists p, q, gcd(p, q) = 1 \land p * a = q * b^2$。 所以
$$a^{qb^2} = b^{qa} \to a^{pa} = b^{qa} \to a^{p} = b^{q}$$
根据同幂相等推公共底数，所以 $\exists c x y, a = c^x, b = c^y$，所以
$(\exists t, b^2 = a t) \lor (\exists k, a = k b^2)$。
首先, 我们设 $\exist t, {b^{2}}={at}$。 由题中等式得 $$a^{2a t}=(a t)^{a},$$ 即 $a^{2 t}=a t$, $t=a^{2 t-1}$。显然 $t > 0$，也说明 $2t - 1 \ge 1$。 则 $$ t=a^{2 t-1} \gt (1+1)^{2 t - 1} \ge 1+(2 t-1)=2 t>t, $$ 矛盾.

接着，我们设 $\exist k, a = k b^2$。由题目等式可得 $$a^{kb^2} = b^{ka} \to a^{a} = b^{ka} \to a = b^k \to k b^2 = b^k$$，即 $k=b^{k-2}$。显然 $k > 0$。

如果 $k = 1$，则 $b^2 = b \to b = 1$，矛盾。

如果 $k = 2$，则 $2b^2 = b^2$，矛盾。

因此 $k = 3$，则 $3b^2 = b^3$，$b=3, a=27$。

如果 $k = 4$, 则 $4b^2 = b^4$, $b=2, a=16$。

> **新增条件 $k > 4$**

- 如果 $b = 2$，则 $k = (1+1)^{k-2} \ge 1 + (k-2) + \frac{(k-2)(k-3)}{2} = 1 + \frac{(k-2)(k-1)}{2} \gt 1 + (k-1) = k$, 矛盾。

- 如果 $b \ge 3$，则 $k = b^{k-2} \ge (1+2)^{k-2} \ge 1+2(k-2) = 2k-3$, 即 $k \le 3$，矛盾。