## Task A-3.2.

Question: 
Determine all pairs of natural numbers $x$ and $y$ for which $\frac{x y^{2}}{x+y}$ is a prime number.

Answer: 
## Rješenje.

Ako je $d=M(x, y)$, možemo pisati $x=d a, y=d b$, pri čemu je $a, b \in \mathbb{N}, M(a, b)=1$.

Neka je $p=\frac{x y^{2}}{x+y}$. Tada je $p=\frac{d a \cdot(d b)^{2}}{d a+d b}$.

Slijedi

$$ d^{2} a b^{2}=p(a+b) $$

Kako je $M(a, a+b)=M(b, a+b)=M(a, b)=1$, zaključujemo da $a b^{2}$ dijeli $p$, što je moguće samo ako je $b=1$ (jednadžba postaje $d^{2} a=p(a+1)$ ) te $a=1$ ili $a=p$.

Razlikujemo dva slučaja:

1. $a=1$

Tada je $d^{2}=2 p$. Kako je $p$ prost broj, slijedi da $p$ dijeli $d$, a time i $p^{2}$ dijeli $d^{2}=2 p$. Odatle zaključujemo da $p^{2}$ dijeli $2 p$, pa $p$ dijeli 2. Stoga je $p=2$ i $d=2$. Jedino rješenje u ovom slučaju je $(x, y)=(2,2)$. 2. $a=p$

Tada je $d^{2}=p+1$, odnosno $(d-1)(d+1)=p$. Kako je $p$ prost broj i $0 \leqslant d-1<$ $d+1$, slijedi $d-1=1$ i $d+1=p$. Odavde je $d=2$ i $p=3$ pa je jedino rješenje u ovom slučaju $(x, y)=(6,2)$.

Konačno, traženi parovi su $(x, y) \in{(2,2),(6,2)}$.




          
我将阅读用户当前打开的文件，以便将其内容翻译成中文。
        
            
toolName: view_files
            
status: success
          
            
filePath: /Users/penglingwei/Documents/prover/lean/project/playground/Markdown/number_theory_247811.md
          
## 任务 A-3.2。

问题：
确定所有的自然数对 $x$ 和 $y$，使得 $\frac{x y^{2}}{x+y}$ 是一个素数。

答案：
## 解答。

如果 $d=M(x, y)$（$M(x,y)$ 表示 $x$ 和 $y$ 的最大公约数），我们可以写成 $x=d a, y=d b$，其中 $a, b \in \mathbb{N}, M(a, b)=1$。

令 $p=\frac{x y^{2}}{x+y}$。那么 $p=\frac{d a \cdot(d b)^{2}}{d a+d b}$。

可得

$$ d^{2} a b^{2}=p(a+b) $$

因为 $M(a, a+b)=M(b, a+b)=M(a, b)=1$，我们得出 $a b^{2}$ 整除 $p$，这只有在 $b=1$（方程变为 $d^{2} a=p(a+1)$）并且 $a=1$ 或 $a=p$ 时才可能。

我们区分两种情况：

1. $a=1$

那么 $d^{2}=2 p$。因为 $p$ 是素数，所以 $p$ 整除 $d$，因此 $p^{2}$ 整除 $d^{2}=2 p$。由此我们得出 $p^{2}$ 整除 $2 p$，所以 $p$ 整除 2。因此 $p=2$ 且 $d=2$。在这种情况下，唯一的解是 $(x, y)=(2,2)$。

2. $a=p$

那么 $d^{2}=p+1$，即 $(d-1)(d+1)=p$。因为 $p$ 是素数且 $0 \leqslant d-1 < d+1$，所以 $d-1=1$ 且 $d+1=p$。由此得到 $d=2$ 且 $p=3$，因此在这种情况下唯一的解是 $(x, y)=(6,2)$。

最后，所求的数对是 $(x, y) \in \{(2,2),(6,2)\}$。
