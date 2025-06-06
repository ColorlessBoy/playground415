Let $A, B, C$ be integers. If $A+B+C$ is an even number, $B$ is divisible by 3, and $A+C$ is divisible by 3, show that the expression $A n^3 + B n^2 + C n$ is divisible by 6 for any integer $n$.

Let $P(n) = A n^3 + B n^2 + C n$. We are given that $A, B, C$ are integers and:

1. $A+B+C$ is an even number, i.e., $A+B+C \\equiv 0 \\pmod 2$.
2. $B$ is divisible by 3, i.e., $B \\equiv 0 \\pmod 3$.
3. $A+C$ is divisible by 3, i.e., $A+C \\equiv 0 \\pmod 3$.

We want to show that $P(n)$ is divisible by 6 for any integer $n$. This is equivalent to showing that $P(n)$ is divisible by 2 and $P(n)$ is divisible by 3 for any integer $n$, since 2 and 3 are coprime.

**Part 1: Show $P(n)$ is divisible by 2 for any integer $n$.**

We consider two cases for the integer $n$:\
Case 1: $n$ is even.\
If $n$ is even, then $n \\equiv 0 \\pmod 2$.\
This implies $n^3 \\equiv 0^3 \\equiv 0 \\pmod 2$, $n^2 \\equiv 0^2 \\equiv 0 \\pmod 2$, and $n \\equiv 0 \\pmod 2$.\
So, $P(n) = A n^3 + B n^2 + C n \\equiv A \\cdot 0 + B \\cdot 0 + C \\cdot 0 \\pmod 2$.\
Thus, $P(n) \\equiv 0 \\pmod 2$.

Case 2: $n$ is odd.\
If $n$ is odd, then $n \\equiv 1 \\pmod 2$.\
This implies $n^3 \\equiv 1^3 \\equiv 1 \\pmod 2$, $n^2 \\equiv 1^2 \\equiv 1 \\pmod 2$, and $n \\equiv 1 \\pmod 2$.\
So, $P(n) = A n^3 + B n^2 + C n \\equiv A \\cdot 1 + B \\cdot 1 + C \\cdot 1 \\pmod 2$.\
$P(n) \\equiv A+B+C \\pmod 2$.\
From condition (1), $A+B+C$ is an even number, so $A+B+C \\equiv 0 \\pmod 2$.\
Thus, $P(n) \\equiv 0 \\pmod 2$.

In both cases ( $n$ even or $n$ odd), $P(n)$ is divisible by 2.

**Part 2: Show $P(n)$ is divisible by 3 for any integer $n$.**

We can rewrite the expression $P(n)$ as follows:\
$P(n) = A n^3 + B n^2 + C n$\
$P(n) = A n^3 - A n + A n + B n^2 + C n$\
$P(n) = A(n^3 - n) + B n^2 + (A+C)n$.

Let's analyze each term:\
Term 1: $A(n^3 - n)$.\
The expression $n^3 - n$ can be factored as $n(n^2-1) = n(n-1)(n+1) = (n-1)n(n+1)$.\
This is the product of three consecutive integers. For any integer $n$, one of these three consecutive integers must be divisible by 3. Therefore, their product $(n-1)n(n+1)$ is always divisible by 3.\
So, $n^3 - n \\equiv 0 \\pmod 3$ for any integer $n$.\
Since $A$ is an integer, $A(n^3 - n)$ is divisible by 3.

Term 2: $B n^2$.\
From condition (2), $B$ is divisible by 3 ($B \\equiv 0 \\pmod 3$).\
Since $n$ is an integer, $n^2$ is an integer.\
Therefore, $B n^2$ is divisible by 3.

Term 3: $(A+C)n$.\
From condition (3), $A+C$ is divisible by 3 ($A+C \\equiv 0 \\pmod 3$).\
Since $n$ is an integer, $(A+C)n$ is divisible by 3.

Since each term in the sum $P(n) = A(n^3 - n) + B n^2 + (A+C)n$ is divisible by 3, their sum $P(n)$ must also be divisible by 3.\
Thus, $P(n) \\equiv 0 \\pmod 3$ for any integer $n$.

**Part 3: Conclude $P(n)$ is divisible by 6.**

We have shown that $P(n)$ is divisible by 2 (from Part 1) and $P(n)$ is divisible by 3 (from Part 2) for any integer $n$.\
Since 2 and 3 are coprime integers (i.e., their greatest common divisor is 1), any integer that is divisible by both 2 and 3 must also be divisible by their product $2 \\cdot 3 = 6$.\
Therefore, $P(n) = A n^3 + B n^2 + C n$ is divisible by 6 for any integer $n$.

The final answer is $\\boxed{A n^3 + B n^2 + C n \\text{ is divisible by } 6}$.


设 $A, B, C$ 为整数。如果 $A+B+C$ 是偶数，$B$ 能被 3 整除，且 $A+C$ 能被 3 整除，证明表达式 $A n^3 + B n^2 + C n$ 对于任意整数 $n$ 都能被 6 整除。

令 $P(n) = A n^3 + B n^2 + C n$。已知 $A, B, C$ 是整数并且：

1. $A+B+C$ 是偶数，即 $A+B+C \equiv 0 \pmod 2$。
2. $B$ 能被 3 整除，即 $B \equiv 0 \pmod 3$。
3. $A+C$ 能被 3 整除，即 $A+C \equiv 0 \pmod 3$。

我们要证明对于任意整数 $n$，$P(n)$ 都能被 6 整除。这等价于证明对于任意整数 $n$，$P(n)$ 能被 2 整除且 $P(n)$ 能被 3 整除，因为 2 和 3 是互质的。

**第一部分：证明对于任意整数 $n$，$P(n)$ 能被 2 整除。**

我们考虑整数 $n$ 的两种情况：
情况 1：$n$ 是偶数。
如果 $n$ 是偶数，则 $n \equiv 0 \pmod 2$。
这意味着 $n^3 \equiv 0^3 \equiv 0 \pmod 2$，$n^2 \equiv 0^2 \equiv 0 \pmod 2$，且 $n \equiv 0 \pmod 2$。
所以，$P(n) = A n^3 + B n^2 + C n \equiv A \cdot 0 + B \cdot 0 + C \cdot 0 \pmod 2$。
因此，$P(n) \equiv 0 \pmod 2$。

情况 2：$n$ 是奇数。
如果 $n$ 是奇数，则 $n \equiv 1 \pmod 2$。
这意味着 $n^3 \equiv 1^3 \equiv 1 \pmod 2$，$n^2 \equiv 1^2 \equiv 1 \pmod 2$，且 $n \equiv 1 \pmod 2$。
所以，$P(n) = A n^3 + B n^2 + C n \equiv A \cdot 1 + B \cdot 1 + C \cdot 1 \pmod 2$。
$P(n) \equiv A+B+C \pmod 2$。
根据条件 (1)，$A+B+C$ 是偶数，所以 $A+B+C \equiv 0 \pmod 2$。
因此，$P(n) \equiv 0 \pmod 2$。

在两种情况下（$n$ 是偶数或 $n$ 是奇数），$P(n)$ 都能被 2 整除。

**第二部分：证明对于任意整数 $n$，$P(n)$ 能被 3 整除。**

我们可以将表达式 $P(n)$改写如下：
$P(n) = A n^3 + B n^2 + C n$
$P(n) = A n^3 - A n + A n + B n^2 + C n$
$P(n) = A(n^3 - n) + B n^2 + (A+C)n$。

让我们分析每一项：
第 1 项：$A(n^3 - n)$。
表达式 $n^3 - n$ 可以分解为 $n(n^2-1) = n(n-1)(n+1) = (n-1)n(n+1)$。
这是三个连续整数的乘积。对于任意整数 $n$，这三个连续整数中必有一个能被 3 整除。因此，它们的乘积 $(n-1)n(n+1)$ 总是能被 3 整除。
所以，对于任意整数 $n$，$n^3 - n \equiv 0 \pmod 3$。
由于 $A$ 是整数，所以 $A(n^3 - n)$ 能被 3 整除。

第 2 项：$B n^2$。
根据条件 (2)，$B$ 能被 3 整除 ($B \equiv 0 \pmod 3$)。
由于 $n$ 是整数，$n^2$ 也是整数。
因此，$B n^2$ 能被 3 整除。

第 3 项：$(A+C)n$。
根据条件 (3)，$A+C$ 能被 3 整除 ($A+C \equiv 0 \pmod 3$)。
由于 $n$ 是整数，$(A+C)n$ 能被 3 整除。

由于和 $P(n) = A(n^3 - n) + B n^2 + (A+C)n$ 中的每一项都能被 3 整除，所以它们的和 $P(n)$ 也必须能被 3 整除。
因此，对于任意整数 $n$，$P(n) \equiv 0 \pmod 3$。

**第三部分：结论 $P(n)$ 能被 6 整除。**

我们已经证明了对于任意整数 $n$，$P(n)$ 能被 2 整除（来自第一部分）且 $P(n)$ 能被 3 整除（来自第二部分）。
由于 2 和 3 是互质整数（即它们的最大公约数是 1），任何能同时被 2 和 3 整除的整数也必须能被它们的乘积 $2 \cdot 3 = 6$ 整除。
因此，对于任意整数 $n$，$P(n) = A n^3 + B n^2 + C n$ 能被 6 整除。

最终答案是 $\boxed{A n^3 + B n^2 + C n \text{能被 } 6 \text{ 整除}}$。
        