6. Define the sequence $\left\{a_{n}\right\}: a_{1}=1, a_{2}=2, a_{n+2}=a_{n}+a_{n+1}, n \in \mathbf{N}_{+}$, then $\left[\frac{a_{2}}{a_{1}}\right] \cdot\left\{\frac{a_{3}}{a_{2}}\right\} \cdot\left\{\frac{a_{4}}{a_{3}}\right\} \cdot \cdots$
- $\left\{\frac{a_{99}}{a_{98}}\right\} \cdot\left[\frac{a_{98}}{a_{2}}\right]$ has the value $(\quad)$
A. 2
B. 0
C. 1
D. $\frac{1}{2}$

6. C 由 $a_{1}=1, a_{2}=2, a_{n+2}=a_{n}+a_{n+1}, n \in \mathbf{N}_{+}$易知对任意 $n \in \mathbf{N}_{+}$均有 $a_{n} \in \mathbf{N}_{+}$, 且 $a_{1}$ $ < a_{2} < \cdots < a_{n} < \cdots$. 从而 $a_{n+2}=a_{n}+a_{n+1} < a_{n+1}+a_{n+1}=2 a_{n+1}$, 即 $\frac{a_{n+2}}{a_{n+1}} < 2$, 所以 $1 < \frac{a_{n+2}}{a_{n+1}} < $ 2. 于是 $\left\{\frac{a_{n+2}}{a_{n+1}}\right\}=\frac{a_{n+2}}{a_{n+1}}-1=\frac{a_{n+1}+a_{n}}{a_{n+1}}-1=\frac{a_{n}}{a_{n+1}}, n \in \mathbf{N}_{+}$. 所以原式 $=\left[\frac{a_{2}}{a_{1}}\right] \cdot\left[\frac{a_{98}}{a_{2}}\right] \cdot \frac{a_{1}}{a_{2}} \cdot$ $\frac{a_{2}}{a_{3}} \cdots \cdots \cdot \frac{a_{97}}{a_{98}}=\left[\frac{a_{2}}{a_{1}}\right] \cdot\left[\frac{a_{98}}{a_{2}}\right] \cdot \frac{a_{1}}{a_{98}}=2 \cdot\left[\frac{a_{98}}{2}\right] \cdot \frac{1}{a_{98}}$. 而由递推式 $a_{n+2}=a_{n}+a_{n+1}$ 及 $a_{1}=1$, $a_{2}=2$ 易通过数学归纳法知 $a_{3 k+2}$ 为偶数, $a_{3 k+1}$ 与 $a_{3 k+3}$ 为奇数 $(k \in \mathbf{N})$, 所以 $a_{98}$ 为偶数, 原式 $=2 \cdot \frac{a_{98}}{2} \cdot \frac{1}{a_{98}}=1$.