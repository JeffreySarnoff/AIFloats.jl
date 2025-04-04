Unit Fractions 1/K and (K–1)/K in Number Theory
Introduction
Unit fractions – fractions with numerator 1 – are the simplest rational numbers, and their complements of the form $(K-1)/K$ (just one unit fraction shy of 1) also yield interesting properties. For example, $1/K$ and $(K-1)/K = 1 - 1/K$ are obviously related (their sum is 1), but this simple relationship belies a rich structure. These forms appear throughout number theory, from ancient Egyptian fraction notation to modern conjectures about rational Diophantine equations. In this report, we explore the properties of $1/K$ and $(K-1)/K$, how they relate to general rational numbers, and their role in various number-theoretic contexts. We will see historical methods of representing fractions using such terms, patterns and identities involving these fractions, and connections to topics like modular arithmetic, Egyptian fractions, and Diophantine equations. Examples and theorems from both classical and contemporary mathematics will illustrate the significance of these simple fractions.
Historical Context: Egyptian Fractions

K=7
1/K == 1/(K+1) + 1/(K * (K+1))


Figure: A portion of the Rhind Mathematical Papyrus (c. 1550 BC), which includes tables decomposing fractions like $2/n$ into unit fractions​
EN.WIKIPEDIA.ORG
.
The ancient Egyptians expressed rational numbers as sums of distinct unit fractions (with a few exceptions for certain forms like $\tfrac{2}{3}$). In their notation, $1/2, 1/3, 1/4, \dots$ were written with special hieroglyphic symbols, and any fraction $\tfrac{a}{b}$ with $a<b$ was represented as a sum of such unit fractions (an Egyptian fraction). Notably, they allowed a couple of non-unit fractions as special cases: they had symbols for $\tfrac{2}{3}$ and $\tfrac{3}{4}$​
EN.WIKIPEDIA.ORG
. In fact, when a fraction larger than $1/2$ needed to be expressed, scribes would often subtract one of these standard complements (like $2/3$ or $3/4$) and then express the remainder as a sum of unit fractions​
EN.WIKIPEDIA.ORG
. For example, $\tfrac{3}{4}$ might be taken as a single summand (since $\tfrac{3}{4} = 1 - \tfrac{1}{4}$ is one unit fraction short of 1), or $\tfrac{2}{3}$ as a summand (since $\tfrac{2}{3} = 1 - \tfrac{1}{3}$). This shows that complements of unit fractions were an integral part of Egyptian representations. A famous example appears in the Rhind Mathematical Papyrus (also called the Ahmes Papyrus, ~1650 BC). The papyrus begins with a table decomposing fractions of the form $2/n$ (for odd $n$ from 3 to 101) into sums of distinct unit fractions​
EN.WIKIPEDIA.ORG
. For instance, it records $\frac{2}{15} = \frac{1}{10} + \frac{1}{30}$​
EN.WIKIPEDIA.ORG
. Remarkably, none of these decompositions used more than 4 terms – even $\frac{2}{101}$ is written as $\frac{1}{101}+\frac{1}{202}+\frac{1}{303}+\frac{1}{606}$​
EN.WIKIPEDIA.ORG
. After the $2/n$ table, the papyrus gives examples of dividing numbers by 10, using $2/3$ as a key part of the representation. It expresses, for example, $\frac{7}{10} = \frac{2}{3} + \frac{1}{30}$​
EN.WIKIPEDIA.ORG
. Here $\tfrac{2}{3}$ (which is $(3-1)/3$) is used as a summand, showing the Egyptian preference for using $(K-1)/K$ forms like $2/3$ to simplify the remainder. (Interestingly, in modern terms $\frac{7}{10}$ could be written more simply as $\frac{1}{2}+\frac{1}{5}$, but the Egyptian approach prioritized known unit-fraction tables and conventions.) These historical examples highlight that unit fractions $1/K$ and their complements $(K-1)/K$ were building blocks of Egyptian mathematical notation​
EN.WIKIPEDIA.ORG
. The use of such fractions had practical motivations: for instance, $\frac{5}{8} = \frac{1}{2} + \frac{1}{8}$ meant that to divide 5 loaves among 8 people, each person could get half a loaf plus an eighth of a loaf​
EN.WIKIPEDIA.ORG
. Using unit fractions (and special cases like $2/3$) made it easier to allocate and measure portions in a pre-decimal society.
Representing Rational Numbers with Unit Fractions
One of the fundamental number-theoretic facts about rational numbers is that any positive rational can be expressed as a sum of distinct unit fractions. In other words, for every fraction $\frac{a}{b}$ (with $0<a<b$) there exists an Egyptian fraction expansion:
𝑎
𝑏
=
1
𝑛
1
+
1
𝑛
2
+
⋯
+
1
𝑛
𝑘
,
b
a
​
 = 
n 
1
​
 
1
​
 + 
n 
2
​
 
1
​
 +⋯+ 
n 
k
​
 
1
​
 ,
where $n_1, n_2, \dots, n_k$ are positive integers, all different. This was implicitly known to the Egyptians and was formally proven in modern terms by Fibonacci (Leonardo of Pisa). In his 1202 book Liber Abaci, Fibonacci described methods to convert any rational number into a sum of unit fractions​
EN.WIKIPEDIA.ORG
. One such method is the greedy algorithm: at each step, take the largest unit fraction not exceeding the remaining fraction. This algorithm (often called Fibonacci’s algorithm) will terminate with an Egyptian fraction representation​
EN.WIKIPEDIA.ORG
​
EN.WIKIPEDIA.ORG
. For example, to expand $\frac{4}{5}$, the greedy method picks the largest unit fraction $\le 4/5$, which is $1/2$. Subtracting, $4/5 - 1/2 = 3/10$. The largest unit fraction $\le 3/10$ is $1/4$. Subtracting, $3/10 - 1/4 = 1/20$. Thus $\frac{4}{5} = \frac{1}{2} + \frac{1}{4} + \frac{1}{20}$, an Egyptian fraction expansion​
R-KNOTT.SURREY.AC.UK
. (In fact, $\frac{4}{5}$ can be written more succinctly as $\frac{1}{2}+\frac{1}{5}+\frac{1}{10}$​
R-KNOTT.SURREY.AC.UK
 – Egyptian fractions are not unique, and there are often many valid representations.) It is now a well-known theorem that every rational number has infinitely many Egyptian fraction representations​
R-KNOTT.SURREY.AC.UK
. Once you find one representation, you can generate more by an identity like $1 = \frac{1}{2}+\frac{1}{3}+\frac{1}{6}$ (which is itself an Egyptian fraction)​
R-KNOTT.SURREY.AC.UK
: for example, substituting $1 = \frac{1}{2}+\frac{1}{3}+\frac{1}{6}$ into any unit fraction $\frac{1}{m}$ yields $\frac{1}{m} = \frac{1}{2m} + \frac{1}{3m} + \frac{1}{6m}$, introducing more terms but still all unit fractions​
R-KNOTT.SURREY.AC.UK
. This shows in principle that each rational number has infinitely many expansions​
R-KNOTT.SURREY.AC.UK
. Two simple identities involving our specific forms $1/K$ and $(K-1)/K$ are worth noting. First, for any $n\ge 2$:
Two-term expansion for $1/n$: $\displaystyle \frac{1}{n} = \frac{1}{n+1} + \frac{1}{n(n+1)}$.
This identity can be verified by finding a common denominator: $\frac{1}{n+1} + \frac{1}{n(n+1)} = \frac{n}{n(n+1)} + \frac{1}{n(n+1)} = \frac{n+1}{n(n+1)} = \frac{1}{n}$. For example, $\frac{1}{4} = \frac{1}{5} + \frac{1}{20}$, and $\frac{1}{10} = \frac{1}{11} + \frac{1}{110}$. This provides a quick way to split any unit fraction into a sum of two smaller unit fractions. Second, from the earlier mentioned Egyptian identity for 1, we have:
Three-term expansion for $1/n$: $\displaystyle \frac{1}{n} = \frac{1}{2n} + \frac{1}{3n} + \frac{1}{6n}$.
This works because $\frac{1}{2n}+\frac{1}{3n}+\frac{1}{6n} = \frac{3+2+1}{6n} = \frac{6}{6n} = \frac{1}{n}$. For example, $\frac{1}{7} = \frac{1}{14}+\frac{1}{21}+\frac{1}{42}$. Interestingly, this shows that any single unit fraction $1/K$ can be represented as a sum of three smaller unit fractions. The denominators $(2K,,3K,,6K)$ in this formula are the first three positive divisors of $6K$, and indeed 6 is a perfect number (equal to the sum of its divisors $1+2+3$), which is why the numerators added up neatly to produce the identity​
R-KNOTT.SURREY.AC.UK
. The complements $(K-1)/K$ can also be expressed as Egyptian fractions. In fact, the Egyptians themselves treated some of these as special cases ($2/3$ and $3/4$ they left as is​
EN.WIKIPEDIA.ORG
, but others like $4/5, 5/6$, etc., they would break down). As a general strategy, one can use the above identities to derive expansions for $(K-1)/K = 1 - \frac{1}{K}$. For example, using the two-term expansion of $1/K$, we get: 
𝐾
−
1
𝐾
=
1
−
1
𝐾
=
1
−
(
1
𝐾
+
1
+
1
𝐾
(
𝐾
+
1
)
)
=
𝐾
𝐾
−
1
𝐾
+
1
−
1
𝐾
(
𝐾
+
1
)
.
K
K−1
​
 =1− 
K
1
​
 =1−( 
K+1
1
​
 + 
K(K+1)
1
​
 )= 
K
K
​
 − 
K+1
1
​
 − 
K(K+1)
1
​
 . Now $\frac{K}{K} = 1$ can itself be written as an Egyptian fraction (for instance $1 = \frac{1}{2}+\frac{1}{3}+\frac{1}{6}$ as given, or any other), so by substituting such an expansion for the 1 on the right-hand side, we can obtain an Egyptian fraction for $(K-1)/K$. There isn’t a single canonical formula for all $(K-1)/K$, but we can illustrate with a few examples:
$\frac{2}{3} = \frac{1}{2} + \frac{1}{6}$ (a classic from the Rhind Papyrus)​
R-KNOTT.SURREY.AC.UK
.
$\frac{3}{4} = \frac{1}{2} + \frac{1}{4}$ (trivial, since $3/4$ already has denominator 4 as one term).
$\frac{4}{5} = \frac{1}{2} + \frac{1}{5} + \frac{1}{10}$ (one of several possibilities​
R-KNOTT.SURREY.AC.UK
).
$\frac{6}{7} = \frac{1}{2} + \frac{1}{3} + \frac{1}{42}$ is one expansion (since $6/7 = 1 - 1/7$ and we used the three-term expansion for $1/7$ here).
In general, representing $(K-1)/K$ may take two or more unit fractions depending on $K$. The “greedy algorithm” will always find some expansion. For instance, if we apply it to $(K-1)/K$: the first term it picks is $1/2$ (because $(K-1)/K < 1$ but is $> 1/2$ for $K>2$). After subtracting $1/2$, the remainder is $(K-1)/K - 1/2 = (2K- (K-1))/2K = (K+1)/2K = \frac{1}{2} + \frac{1}{2K}$. So one gets $(K-1)/K = 1/2 + 1/2K$. If $K=3$, this gives $2/3 = 1/2 + 1/6$ as above; if $K=5$, it gives $4/5 = 1/2 + 1/10$ (but we’d still have $4/5 - (1/2+1/10) = 1/5$ left over, so actually the greedy algorithm would then add $1/5$ to finish the job). In any case, the key takeaway is that $1/K$ and $1 - 1/K$ are not just reciprocals and complements in the trivial sense, but also act as fundamental pieces that can generate other rational numbers through Egyptian expansions. This is why historically they were tabulated and studied.
Patterns in Modular Arithmetic and Repeating Decimals
Unit fractions have a natural connection to modular arithmetic, especially when we consider their decimal (or other base) expansions. If $K$ is coprime to 10, the decimal expansion of $1/K$ will be repeating (non-terminating), and its repetend (the repeating block of digits) is intimately related to the multiplicative order of 10 modulo $K$. In fact, the length of the repeating cycle of $1/K$ is the smallest positive integer $d$ such that $10^d \equiv 1 \pmod{K}$. For example, $1/7 = 0.\overline{142857}$ has a repetend of length 6, and indeed $10^6 = 1,000,000 \equiv 1 \pmod{7}$. The repeating digits 142857 are not random; they form what is known as a cyclic number. Multiplying 142857 by any number from 2 through 6 permutes its digits (e.g. $142857 \times 2 = 285714$), reflecting the fact that $2/7, 3/7, ..., 6/7$ produce cyclic permutations of the same repetend. In particular, $\frac{6}{7} = 0.\overline{857142}$, which is exactly the “complement” of $0.\overline{142857}$ in the sense that $0.\overline{142857} + 0.\overline{857142} = 0.\overline{999999} = 0.999999\ldots = 1$. Generally, for a denominator $K$ (coprime to the base), $1/K$ and $(K-1)/K$ have repeating decimals that are complements of each other: digit by digit, they sum to 9 (in base 10). Another simple example: $1/3 = 0.\overline{3}$ and $2/3 = 0.\overline{6}$; indeed $3+6=9$ in each repeating digit. Similarly, $1/11 = 0.\overline{09}$ and $10/11 = 0.\overline{90}$. This pattern arises because $(K-1)/K = 1 - 1/K$, so its decimal expansion is the subtraction of $0.\overline{\text{(repetend of }1/K)}$ from 1, which yields the 9’s complement repetend. In modular arithmetic terms, saying $10^d \equiv 1 \pmod{K}$ means $K$ divides $10^d - 1$, so $1/K = \frac{A}{10^d - 1}$ for some integer $A$. Here $10^d-1$ is a number like 99...9 (d digits of 9), and indeed $A$ will be the integer formed by the repetend digits. For example, $1/7 = 142857/999999$ and $6/7 = 857142/999999$. This is a clear algebraic relation between a fraction and its repeating pattern. Beyond base-10 patterns, unit fractions also connect to general modular inverses. The number $1/K$ (as a rational number) corresponds to the multiplicative inverse of $K$ in the ring of integers modulo $m$, if $\gcd(K,m)=1$. For instance, $1/K \pmod{p}$ (for $p$ prime not dividing $K$) is the unique number $x$ such that $Kx \equiv 1 \pmod{p}$. This is essentially Fermat’s little theorem in action: one can show $K^{p-1} \equiv 1 \pmod{p}$, hence $K^{p-2} \equiv K^{-1} \pmod{p}$, meaning $x = K^{p-2}$ is the residue corresponding to $1/K$. One interesting property here is that the sum of all such modular reciprocals in a prime field has a nice result: for a prime $p>2$, 
1
+
1
2
+
1
3
+
⋯
+
1
𝑝
−
1
≡
0
(
m
o
d
𝑝
)
,
1+ 
2
1
​
 + 
3
1
​
 +⋯+ 
p−1
1
​
 ≡0(modp), when interpreted modulo $p$. This is because the set ${1^{-1},2^{-1},\dots,(p-1)^{-1}}$ is just a permutation of ${1,2,\dots,p-1}$ modulo $p$. For example, mod 7: $1+1/2+1/3+1/4+1/5+1/6 \equiv 1+4+5+2+3+6 = 21 \equiv 0 \pmod{7}$. A far deeper result along these lines is Wolstenholme’s theorem (1862), which states that for any prime $p>3$, the numerator of $1 + \frac{1}{2} + \cdots + \frac{1}{p-1}$ (when written in lowest terms) is divisible by $p^2$. This implies a congruence like $1 + \frac{1}{2} + \cdots + \frac{1}{p-1} \equiv 0 \pmod{p^2}$ in a certain well-defined sense. Although not directly about $1/K$ vs $(K-1)/K$, Wolstenholme’s theorem underscores the special role of unit fractions summing up in modular arithmetic contexts. In summary, the forms $1/K$ and $(K-1)/K$ show up in base-dependent patterns (like repeating decimals) and base-independent congruences (like properties of harmonic sums mod $p$). The complement pair $1/K$ and $(K-1)/K$ often exhibit symmetry: one might call $(K-1)/K$ the “9’s complement” of $1/K$ in decimal, or in any base the analogous complement to the full reptend.
Diophantine Equations and Egyptian Fraction Problems
Expressions involving sums of unit fractions naturally lead to Diophantine equations. A classic example is the equation: 
1
𝑥
+
1
𝑦
=
1
𝑛
,
x
1
​
 + 
y
1
​
 = 
n
1
​
 , with $x,y,n$ positive integers. Solving this is equivalent to finding an Egyptian fraction representation of $1/n$ with two terms. Clearing denominators gives $xy$ as a multiple of $n$: 
1
𝑥
+
1
𝑦
=
1
𝑛
  
⟺
  
𝑥
+
𝑦
𝑥
𝑦
=
1
𝑛
  
⟺
  
𝑥
𝑦
=
𝑛
(
𝑥
+
𝑦
)
.
x
1
​
 + 
y
1
​
 = 
n
1
​
 ⟺ 
xy
x+y
​
 = 
n
1
​
 ⟺xy=n(x+y). Rearrange to $xy - nx - ny = 0$ or $(x-n)(y-n) = n^2$. Thus solutions correspond to pairs of divisors of $n^2$. For each divisor $d$ of $n^2$, one can set $x-n = d$ and $y-n = \frac{n^2}{d}$, yielding $x = d+n$ and $y = \frac{n^2}{d} + n$. This describes all solutions in positive integers. For example, with $n=4$: $(x-4)(y-4)=16$. The divisors of 16 give solutions like $x-4=1, y-4=16$ (so $x=5, y=20$) corresponding to $1/5+1/20=1/4$; or $x-4=2, y-4=8$ (so $x=6,y=12$) giving $1/6+1/12=1/4$; or $x-4=4,y-4=4$ ($x=y=8$) giving $1/8+1/8=1/4$. That last solution uses a repeated unit fraction, which Egyptians would not allow, but mathematically it’s a valid solution of the equation. We see there are infinitely many representations of $\frac{1}{4}$ if we allowed repetition, but with the distinctness restriction we have finitely many (in this case two: $1/5+1/20$ and $1/6+1/12$) because $(x,y)$ and $(y,x)$ are considered the same representation for Egyptian fractions. This kind of analysis can be extended to equations with more terms, but it becomes much more complex. One famous problem in this vein is the Erdős–Straus conjecture (1948), which focuses on representations of $\frac{4}{n}$ as a sum of three unit fractions. The conjecture asserts that for every integer $n\ge 2$, there exist positive integers $x,y,z$ such that: 
4
𝑛
=
1
𝑥
+
1
𝑦
+
1
𝑧
.
n
4
​
 = 
x
1
​
 + 
y
1
​
 + 
z
1
​
 . In other words, $\frac{4}{n}$ has an Egyptian fraction expansion of length 3 (not necessarily with distinct denominators, though one can often make them distinct). Despite extensive effort, this conjecture remains unproven in full generality – it is one of the longest-standing open problems about Egyptian fractions. It has been verified by computer for very large $n$ (all $n < 10^{17}$, as well as “almost all” $n$ beyond that range)​
EN.WIKIPEDIA.ORG
, but a general proof is unknown. The conjecture is interesting because $\frac{4}{n}$ is $(n-4)/n$ plus a bit more complexity; why the numerator 4? It appears that 4 is the smallest integer where the property of always having a 3-term expansion might be hard to guarantee – for $\frac{3}{n}$, it’s known to be always possible with at most 3 terms, as we’ll discuss next. Erdős and Straus allowing repeated denominators means they considered solutions to $4/n = 1/x+1/y+1/z$ in positive integers without the distinctness condition (one could have $x=y$ for instance). However, any solution with a repeat can be transformed into a solution with distinct terms (usually with more terms) by a transformation akin to the one by Takenouchi (1921)​
EN.WIKIPEDIA.ORG
. Empirical evidence strongly suggests Erdős–Straus is true – no counterexample has been found up to very large $n$​
EN.WIKIPEDIA.ORG
 – but it exemplifies how a simple question about unit fractions leads to deep difficulties. What about $\frac{3}{n}$ or other numerators? If $n$ is a multiple of 3, $\frac{3}{n}$ is itself a unit fraction ($=1/(n/3)$), so the interesting cases are when $3\nmid n$. In 2000, Timothy Hagedorn proved that if $n$ is not divisible by 3 and is odd, then $\frac{3}{n}$ can always be written as a sum of three distinct odd unit fractions​
R-KNOTT.SURREY.AC.UK
. For example, $\frac{3}{5} = \frac{1}{2} + \frac{1}{5} + \frac{1}{10}$ (here one denominator is even, 10, so not all odd in this representation; Hagedorn’s theorem would guarantee a representation like $\frac{3}{5} = \frac{1}{3} + \frac{1}{4} + \frac{1}{60}$ which uses only odd denominators except the 4… perhaps a better example: $\frac{3}{7} = \frac{1}{3} + \frac{1}{11} + \frac{1}{231}$ uses odd denominators 3,11,231). If $n$ is even and not a multiple of 3, $\frac{3}{n}$ also appears always to have a 3-term expansion (often even a 2-term one, e.g. $\frac{3}{10} = \frac{1}{4}+\frac{1}{20}$). In fact, it’s known that every $\frac{3}{n}$ has a three-term expansion (with the possible exception of some even $n$ that are powers of 2, which trivially don’t since $\frac{3}{2^k}$ reduces to $\frac{3}{2^k}$ and needs at least 3 terms). The case for $\frac{5}{n}$ and others grows progressively harder; there is no known simple criterion like the Erdős–Straus conjecture for 5, but computations suggest $\frac{5}{n}$ often needs at most 4 terms. Research continues into these kinds of problems, and they blend techniques from number theory, algebra, and computational search. Another intriguing result in this domain was the Erdős–Graham conjecture (proposed in 1980 by Paul Erdős and Ronald Graham), which was solved in 2003. This was not about a single fraction but about partitioning the integers. It stated that if the positive integers greater than 1 are arbitrarily partitioned into finitely many subsets, one of those subsets will contain an “Egyptian fraction” sum that equals 1​
EN.WIKIPEDIA.ORG
. In plain terms: no matter how you color the integers in a fixed number of colors, you can always find a monochromatic set of numbers ${d_1,\dots,d_k}$ such that $\frac{1}{d_1}+\cdots+\frac{1}{d_k}=1$. This was proved by Ernie Croot in 2003​
EN.WIKIPEDIA.ORG
, confirming a deep fact about unit fractions summing to 1. Notice the sum to 1 can be seen as a special case of the complement idea: summing to 1 means you’ve perfectly expressed 1 (which is $N/N$ for any $N$) as an Egyptian fraction. Indeed, expressing 1 itself as an Egyptian fraction has a tie to number theory: a number $N$ is perfect if $1 + \frac{1}{2} + \cdots + \frac{1}{N-1} = 1$ when restricting the sum to divisors of $N$. For example, 6 is perfect because $6 = 1+2+3$, which yields $1 = 1/2 + 1/3 + 1/6$. 28 is perfect (divisors $1+2+4+7+14=28$) giving $1 = 1/2+1/4+1/7+1/14+1/28$. More generally, primary pseudoperfect numbers are those that allow an Egyptian fraction of 1 that includes the number itself in the denominators. An example is 1806, which has the property $1806 = 2 \times 3 \times 7 \times 43$ divides something and indeed $1 = 1/2 + 1/3 + 1/7 + 1/43 + 1/1806$​
EN.WIKIPEDIA.ORG
. These esoteric patterns show how unit fractions intersect with the theory of divisors and special integers. Finally, a word on computational complexity: finding an Egyptian fraction representation (without additional constraints) is easy via the greedy algorithm, but finding one that minimizes the number of terms or the largest denominator is much harder. No efficient algorithm is known to minimize the number of terms; the search space seems to grow quickly, and it’s suspected that these minimization problems might be NP-hard (though it remains unproven)​
EN.WIKIPEDIA.ORG
. The Egyptian fraction problem has many open questions: Are there efficient algorithms to find expansions with, say, the least maximum denominator? How few terms are needed in general to represent any $a/b$ (a conjecture by Erdős posited $O(\log b)$ terms always suffice; tighter conjectures say maybe $O(\log\log b)$ terms are enough​
EN.WIKIPEDIA.ORG
)? Such problems remain active areas of research, bridging number theory and computer science.
Conclusion
The simple fractions $1/K$ and $(K-1)/K$ serve as fundamental building blocks in number theory and its applications. From ancient times, they were the basis of representing all rational numbers as sums of unit fractions – a practice that, while no longer used for practical arithmetic, has inspired deep theoretical questions. We’ve seen that every rational number can be composed from unit fractions, often starting with a term like $1/K$ or $(K-1)/K$ to approximate the target and then refining the remainder. These fractions show elegant patterns: Egyptian fraction identities, complementary repeating decimals, and modular relationships. They also lead to challenging Diophantine equations: finding integers $x,y,z,\dots$ such that $\frac{a}{b} = \frac{1}{x}+\frac{1}{y}+\cdots$ is a classical problem with many unsolved cases (like the Erdős–Straus conjecture for $4/n$​
EN.WIKIPEDIA.ORG
). On the other hand, much progress has been made – for instance, every fraction with odd denominator has an expansion using odd unit fractions​
EN.WIKIPEDIA.ORG
, and every large enough integer can be partitioned to yield an Egyptian sum for 1​
EN.WIKIPEDIA.ORG
. In a way, exploring $1/K$ and $(K-1)/K$ is exploring how the number 1 can be broken into harmonious parts. The ancient Egyptians might have seen it as practical arithmetic and fair division, while modern mathematicians see combinatorial structures and infinite possibilities. These tiny fractions connect the very concrete (sharing 5 pizzas among 8 people) to the very abstract (coloring integers or analyzing prime divisors). The fascination of unit fractions endures – a testament to how even the simplest components of arithmetic hide endless patterns and puzzles in their reciprocals. Sources: Historical details from the Rhind Papyrus and Egyptian fraction usage​
EN.WIKIPEDIA.ORG
​
EN.WIKIPEDIA.ORG
​
EN.WIKIPEDIA.ORG
; Fibonacci’s greedy algorithm and identities​
EN.WIKIPEDIA.ORG
​
R-KNOTT.SURREY.AC.UK
; examples of expansions​
R-KNOTT.SURREY.AC.UK
​
R-KNOTT.SURREY.AC.UK
; modern results on Egyptian fractions and conjectures​
R-KNOTT.SURREY.AC.UK
​
EN.WIKIPEDIA.ORG
​
EN.WIKIPEDIA.ORG
​
EN.WIKIPEDIA.ORG
.
Patterns in Modular Arithmetic and Repeating Decimals
Unit fractions have a natural connection to modular arithmetic, especially when we consider their decimal (or other base) expansions. If $K$ is coprime to 10, the decimal expansion of $1/K$ will be repeating (non-terminating), and its repetend (the repeating block of digits) is intimately related to the multiplicative order of 10 modulo $K$. In fact, the length of the repeating cycle of $1/K$ is the smallest positive integer $d$ such that $10^d \equiv 1 \pmod{K}$. For example, $1/7 = 0.\overline{142857}$ has a repetend of length 6, and indeed $10^6 = 1,000,000 \equiv 1 \pmod{7}$. The repeating digits 142857 are not random; they form what is known as a cyclic number. Multiplying 142857 by any number from 2 through 6 permutes its digits (e.g. $142857 \times 2 = 285714$), reflecting the fact that $2/7, 3/7, ..., 6/7$ produce cyclic permutations of the same repetend. In particular, $\frac{6}{7} = 0.\overline{857142}$, which is exactly the “complement” of $0.\overline{142857}$ in the sense that $0.\overline{142857} + 0.\overline{857142} = 0.\overline{999999} = 0.999999\ldots = 1$. Generally, for a denominator $K$ (coprime to the base), $1/K$ and $(K-1)/K$ have repeating decimals that are complements of each other: digit by digit, they sum to 9 (in base 10). Another simple example: $1/3 = 0.\overline{3}$ and $2/3 = 0.\overline{6}$; indeed $3+6=9$ in each repeating digit. Similarly, $1/11 = 0.\overline{09}$ and $10/11 = 0.\overline{90}$. This pattern arises because $(K-1)/K = 1 - 1/K$, so its decimal expansion is the subtraction of $0.\overline{\text{(repetend of }1/K)}$ from 1, which yields the 9’s complement repetend. In modular arithmetic terms, saying $10^d \equiv 1 \pmod{K}$ means $K$ divides $10^d - 1$, so $1/K = \frac{A}{10^d - 1}$ for some integer $A$. Here $10^d-1$ is a number like 99...9 (d digits of 9), and indeed $A$ will be the integer formed by the repetend digits. For example, $1/7 = 142857/999999$ and $6/7 = 857142/999999$. This is a clear algebraic relation between a fraction and its repeating pattern. Beyond base-10 patterns, unit fractions also connect to general modular inverses. The number $1/K$ (as a rational number) corresponds to the multiplicative inverse of $K$ in the ring of integers modulo $m$, if $\gcd(K,m)=1$. For instance, $1/K \pmod{p}$ (for $p$ prime not dividing $K$) is the unique number $x$ such that $Kx \equiv 1 \pmod{p}$. This is essentially Fermat’s little theorem in action: one can show $K^{p-1} \equiv 1 \pmod{p}$, hence $K^{p-2} \equiv K^{-1} \pmod{p}$, meaning $x = K^{p-2}$ is the residue corresponding to $1/K$. One interesting property here is that the sum of all such modular reciprocals in a prime field has a nice result: for a prime $p>2$, 
1
+
1
2
+
1
3
+
⋯
+
1
𝑝
−
1
≡
0
(
m
o
d
𝑝
)
,
1+ 
2
1
​
 + 
3
1
​
 +⋯+ 
p−1
1
​
 ≡0(modp), when interpreted modulo $p$. This is because the set ${1^{-1},2^{-1},\dots,(p-1)^{-1}}$ is just a permutation of ${1,2,\dots,p-1}$ modulo $p$. For example, mod 7: $1+1/2+1/3+1/4+1/5+1/6 \equiv 1+4+5+2+3+6 = 21 \equiv 0 \pmod{7}$. A far deeper result along these lines is Wolstenholme’s theorem (1862), which states that for any prime $p>3$, the numerator of $1 + \frac{1}{2} + \cdots + \frac{1}{p-1}$ (when written in lowest terms) is divisible by $p^2$. This implies a congruence like $1 + \frac{1}{2} + \cdots + \frac{1}{p-1} \equiv 0 \pmod{p^2}$ in a certain well-defined sense. Although not directly about $1/K$ vs $(K-1)/K$, Wolstenholme’s theorem underscores the special role of unit fractions summing up in modular arithmetic contexts. In summary, the forms $1/K$ and $(K-1)/K$ show up in base-dependent patterns (like repeating decimals) and base-independent congruences (like properties of harmonic sums mod $p$). The complement pair $1/K$ and $(K-1)/K$ often exhibit symmetry: one might call $(K-1)/K$ the “9’s complement” of $1/K$ in decimal, or in any base the analogous complement to the full reptend.
Diophantine Equations and Egyptian Fraction Problems
Expressions involving sums of unit fractions naturally lead to Diophantine equations. A classic example is the equation: 
1
𝑥
+
1
𝑦
=
1
𝑛
,
x
1
​
 + 
y
1
​
 = 
n
1
​
 , with $x,y,n$ positive integers. Solving this is equivalent to finding an Egyptian fraction representation of $1/n$ with two terms. Clearing denominators gives $xy$ as a multiple of $n$: 
1
𝑥
+
1
𝑦
=
1
𝑛
  
⟺
  
𝑥
+
𝑦
𝑥
𝑦
=
1
𝑛
  
⟺
  
𝑥
𝑦
=
𝑛
(
𝑥
+
𝑦
)
.
x
1
​
 + 
y
1
​
 = 
n
1
​
 ⟺ 
xy
x+y
​
 = 
n
1
​
 ⟺xy=n(x+y). Rearrange to $xy - nx - ny = 0$ or $(x-n)(y-n) = n^2$. Thus solutions correspond to pairs of divisors of $n^2$. For each divisor $d$ of $n^2$, one can set $x-n = d$ and $y-n = \frac{n^2}{d}$, yielding $x = d+n$ and $y = \frac{n^2}{d} + n$. This describes all solutions in positive integers. For example, with $n=4$: $(x-4)(y-4)=16$. The divisors of 16 give solutions like $x-4=1, y-4=16$ (so $x=5, y=20$) corresponding to $1/5+1/20=1/4$; or $x-4=2, y-4=8$ (so $x=6,y=12$) giving $1/6+1/12=1/4$; or $x-4=4,y-4=4$ ($x=y=8$) giving $1/8+1/8=1/4$. That last solution uses a repeated unit fraction, which Egyptians would not allow, but mathematically it’s a valid solution of the equation. We see there are infinitely many representations of $\frac{1}{4}$ if we allowed repetition, but with the distinctness restriction we have finitely many (in this case two: $1/5+1/20$ and $1/6+1/12$) because $(x,y)$ and $(y,x)$ are considered the same representation for Egyptian fractions. This kind of analysis can be extended to equations with more terms, but it becomes much more complex. One famous problem in this vein is the Erdős–Straus conjecture (1948), which focuses on representations of $\frac{4}{n}$ as a sum of three unit fractions. The conjecture asserts that for every integer $n\ge 2$, there exist positive integers $x,y,z$ such that: 
4
𝑛
=
1
𝑥
+
1
𝑦
+
1
𝑧
.
n
4
​
 = 
x
1
​
 + 
y
1
​
 + 
z
1
​
 . In other words, $\frac{4}{n}$ has an Egyptian fraction expansion of length 3 (not necessarily with distinct denominators, though one can often make them distinct). Despite extensive effort, this conjecture remains unproven in full generality – it is one of the longest-standing open problems about Egyptian fractions. It has been verified by computer for very large $n$ (all $n < 10^{17}$, as well as “almost all” $n$ beyond that range)​
EN.WIKIPEDIA.ORG
, but a general proof is unknown. The conjecture is interesting because $\frac{4}{n}$ is $(n-4)/n$ plus a bit more complexity; why the numerator 4? It appears that 4 is the smallest integer where the property of always having a 3-term expansion might be hard to guarantee – for $\frac{3}{n}$, it’s known to be always possible with at most 3 terms, as we’ll discuss next. Erdős and Straus allowing repeated denominators means they considered solutions to $4/n = 1/x+1/y+1/z$ in positive integers without the distinctness condition (one could have $x=y$ for instance). However, any solution with a repeat can be transformed into a solution with distinct terms (usually with more terms) by a transformation akin to the one by Takenouchi (1921)​
EN.WIKIPEDIA.ORG
. Empirical evidence strongly suggests Erdős–Straus is true – no counterexample has been found up to very large $n$​
EN.WIKIPEDIA.ORG
 – but it exemplifies how a simple question about unit fractions leads to deep difficulties. What about $\frac{3}{n}$ or other numerators? If $n$ is a multiple of 3, $\frac{3}{n}$ is itself a unit fraction ($=1/(n/3)$), so the interesting cases are when $3\nmid n$. In 2000, Timothy Hagedorn proved that if $n$ is not divisible by 3 and is odd, then $\frac{3}{n}$ can always be written as a sum of three distinct odd unit fractions​
R-KNOTT.SURREY.AC.UK
. For example, $\frac{3}{5} = \frac{1}{2} + \frac{1}{5} + \frac{1}{10}$ (here one denominator is even, 10, so not all odd in this representation; Hagedorn’s theorem would guarantee a representation like $\frac{3}{5} = \frac{1}{3} + \frac{1}{4} + \frac{1}{60}$ which uses only odd denominators except the 4… perhaps a better example: $\frac{3}{7} = \frac{1}{3} + \frac{1}{11} + \frac{1}{231}$ uses odd denominators 3,11,231). If $n$ is even and not a multiple of 3, $\frac{3}{n}$ also appears always to have a 3-term expansion (often even a 2-term one, e.g. $\frac{3}{10} = \frac{1}{4}+\frac{1}{20}$). In fact, it’s known that every $\frac{3}{n}$ has a three-term expansion (with the possible exception of some even $n$ that are powers of 2, which trivially don’t since $\frac{3}{2^k}$ reduces to $\frac{3}{2^k}$ and needs at least 3 terms). The case for $\frac{5}{n}$ and others grows progressively harder; there is no known simple criterion like the Erdős–Straus conjecture for 5, but computations suggest $\frac{5}{n}$ often needs at most 4 terms. Research continues into these kinds of problems, and they blend techniques from number theory, algebra, and computational search. Another intriguing result in this domain was the Erdős–Graham conjecture (proposed in 1980 by Paul Erdős and Ronald Graham), which was solved in 2003. This was not about a single fraction but about partitioning the integers. It stated that if the positive integers greater than 1 are arbitrarily partitioned into finitely many subsets, one of those subsets will contain an “Egyptian fraction” sum that equals 1​
EN.WIKIPEDIA.ORG
. In plain terms: no matter how you color the integers in a fixed number of colors, you can always find a monochromatic set of numbers ${d_1,\dots,d_k}$ such that $\frac{1}{d_1}+\cdots+\frac{1}{d_k}=1$. This was proved by Ernie Croot in 2003​
EN.WIKIPEDIA.ORG
, confirming a deep fact about unit fractions summing to 1. Notice the sum to 1 can be seen as a special case of the complement idea: summing to 1 means you’ve perfectly expressed 1 (which is $N/N$ for any $N$) as an Egyptian fraction. Indeed, expressing 1 itself as an Egyptian fraction has a tie to number theory: a number $N$ is perfect if $1 + \frac{1}{2} + \cdots + \frac{1}{N-1} = 1$ when restricting the sum to divisors of $N$. For example, 6 is perfect because $6 = 1+2+3$, which yields $1 = 1/2 + 1/3 + 1/6$. 28 is perfect (divisors $1+2+4+7+14=28$) giving $1 = 1/2+1/4+1/7+1/14+1/28$. More generally, primary pseudoperfect numbers are those that allow an Egyptian fraction of 1 that includes the number itself in the denominators. An example is 1806, which has the property $1806 = 2 \times 3 \times 7 \times 43$ divides something and indeed $1 = 1/2 + 1/3 + 1/7 + 1/43 + 1/1806$​
EN.WIKIPEDIA.ORG
. These esoteric patterns show how unit fractions intersect with the theory of divisors and special integers. Finally, a word on computational complexity: finding an Egyptian fraction representation (without additional constraints) is easy via the greedy algorithm, but finding one that minimizes the number of terms or the largest denominator is much harder. No efficient algorithm is known to minimize the number of terms; the search space seems to grow quickly, and it’s suspected that these minimization problems might be NP-hard (though it remains unproven)​
EN.WIKIPEDIA.ORG
. The Egyptian fraction problem has many open questions: Are there efficient algorithms to find expansions with, say, the least maximum denominator? How few terms are needed in general to represent any $a/b$ (a conjecture by Erdős posited $O(\log b)$ terms always suffice; tighter conjectures say maybe $O(\log\log b)$ terms are enough​
EN.WIKIPEDIA.ORG
)? Such problems remain active areas of research, bridging number theory and computer science.
Conclusion
The simple fractions $1/K$ and $(K-1)/K$ serve as fundamental building blocks in number theory and its applications. From ancient times, they were the basis of representing all rational numbers as sums of unit fractions – a practice that, while no longer used for practical arithmetic, has inspired deep theoretical questions. We’ve seen that every rational number can be composed from unit fractions, often starting with a term like $1/K$ or $(K-1)/K$ to approximate the target and then refining the remainder. These fractions show elegant patterns: Egyptian fraction identities, complementary repeating decimals, and modular relationships. They also lead to challenging Diophantine equations: finding integers $x,y,z,\dots$ such that $\frac{a}{b} = \frac{1}{x}+\frac{1}{y}+\cdots$ is a classical problem with many unsolved cases (like the Erdős–Straus conjecture for $4/n$​
EN.WIKIPEDIA.ORG
). On the other hand, much progress has been made – for instance, every fraction with odd denominator has an expansion using odd unit fractions​
EN.WIKIPEDIA.ORG
, and every large enough integer can be partitioned to yield an Egyptian sum for 1​
EN.WIKIPEDIA.ORG
. In a way, exploring $1/K$ and $(K-1)/K$ is exploring how the number 1 can be broken into harmonious parts. The ancient Egyptians might have seen it as practical arithmetic and fair division, while modern mathematicians see combinatorial structures and infinite possibilities. These tiny fractions connect the very concrete (sharing 5 pizzas among 8 people) to the very abstract (coloring integers or analyzing prime divisors). The fascination of unit fractions endures – a testament to how even the simplest components of arithmetic hide endless patterns and puzzles in their reciprocals.
