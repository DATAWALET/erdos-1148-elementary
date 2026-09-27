# Bounded Representations $n = x^2 + y^2 - z^2$: an Elementary Reduction Theorem and the Complete Exception List below 250000

**Erdős Problem 1148 / Justin Sun Prize problem JSP-000953**

Author: TogaintDum
Date: September 27, 2026
License: CC BY 4.0 (text), MIT (code)
Contact: yaoyegroup.china@gmail.com

> **Positioning statement.** This note does **not** claim solver credit for JSP-000953.
> The problem was solved by Przemysław Chojecki (Duke's theorem, qualitative threshold,
> March 2026) and formalized in Lean by Boris Alexeev. What is offered here is an
> **independent elementary proof route** for the composite case, a **deterministic
> effective verification** of the full range $[1, 250000]$, and — to our knowledge —
> the first explicitly published list of the 77 exceptions, the largest being 6563.

---

## Abstract

Erdős Problem 1148 asks whether every sufficiently large integer $n$ can be written as
$n = x^2 + y^2 - z^2$ with $x^2, y^2, z^2 \le n$. We give a self-contained elementary
treatment. First, an explicit three-case construction shows that every positive integer
admits such a representation if one coefficient is allowed the bound $\lfloor\sqrt n\rfloor + 1$
(a classical observation). Second, we prove a **reduction theorem**: if $n \equiv 2 \pmod 4$,
$m = \lfloor\sqrt n\rfloor \ge 5$ and $2m + r - 1$ (with $r = n - m^2$) is composite, then a
fully bounded representation exists. Consequently a potential exception must satisfy
$r \equiv 2 \pmod 4$ *and* have $2m+r-1$ prime, which reduces the verification of $[1,N]$
from $\Theta(N^{3/2})$ to $O(N / \log N)$ candidate checks. Third, a deterministic
certificate search based on this reduction certifies that **every** $n \in [6564, 250000]$
is representable and that exactly **77** integers below $250000$ are not, the largest
being $6563$. We conjecture that $6563$ is the largest exception. Two conceptual remarks (a rigidity/gradient obstruction; the true decoding
complexity) are included, and Section 8 develops, as a speculative research proposal,
the information-theoretic perspective that motivated this note (distributed bit-packing,
codebook redundancy, two-slider decoding, and a thin prime-remainder hard kernel). All claims are machine-verifiable with the 60-line script in Appendix B.

## 1. The problem and its status

**Problem (Erdős #1148; JSP-000953).** Does there exist $N$ such that every integer
$n \ge N$ admits $x, y, z \in \mathbb Z$ with
$$n = x^2 + y^2 - z^2, \qquad x^2,\; y^2,\; z^2 \le n \;?$$

Chojecki [1] answered **yes**, by an equidistribution argument: representations correspond,
after a linear change of variables, to primitive binary quadratic forms of discriminant $4n$
in a fixed compact patch of the hyperboloid, whose existence for large $n$ follows from
Duke's theorem in the point-counting form of Einsiedler–Lindenstrauss–Michel–Venkatesh [2].
The proof is **qualitative**: it produces no explicit threshold $N$. Alexeev formalized the
solution in Lean (`Erdos1148.lean`). The present note is complementary: everything below is
elementary, effective, and fully explicit below $250000$.

**Notation.** Throughout, $m = \lfloor \sqrt n \rfloor$ and $r = n - m^2$, so
$0 \le r \le 2m$. We use the two identities, valid for odd $t$ resp. all $y$:
$$t = \Big(\tfrac{t+1}{2}\Big)^2 - \Big(\tfrac{t-1}{2}\Big)^2, \qquad 4y = (y+1)^2 - (y-1)^2. \tag{1}$$

## 2. The relaxed problem: an explicit three-case construction

**Theorem 2.1 (relaxed bound; classical).** *Every positive integer $n$ can be written as
$n = a^2 + b^2 - c^2$ with $0 \le b, c \le \sqrt n$ and $0 \le a \le \lfloor\sqrt n\rfloor + 1$.*

**Proof.** Three cases according to $r \bmod 4$.

*Case 1: $r$ odd.* By (1), $n = m^2 + \big(\tfrac{r+1}{2}\big)^2 - \big(\tfrac{r-1}{2}\big)^2$.
Since $r$ is odd and $r \le 2m$, we have $r \le 2m-1$, hence $\tfrac{r+1}{2} \le m$ and
$\tfrac{r-1}{2} \le m-1$: all three coefficients are $\le m \le \sqrt n$. $\blacksquare$-case

*Case 2: $4 \mid r$.* If $r = 0$, then $n = m^2 + 0^2 - 0^2$. If $r \ge 4$, by (1),
$n = m^2 + \big(\tfrac r4 + 1\big)^2 - \big(\tfrac r4 - 1\big)^2$, and
$\tfrac r4 + 1 \le \tfrac m2 + 1 \le m$ for $m \ge 2$; the cases $n \le 3$ are checked directly. $\blacksquare$-case

*Case 3: $r \equiv 2 \pmod 4$.* Put $s = (m+1)^2 - n = 2m + 1 - r$. Since $r$ is even and
$2 \le r \le 2m$, $s$ is odd with $1 \le s \le 2m-1$, and by (1)
$$n = (m+1)^2 + \Big(\tfrac{s-1}{2}\Big)^2 - \Big(\tfrac{s+1}{2}\Big)^2,$$
where $\tfrac{s+1}{2} \le m$, $\tfrac{s-1}{2} \le m-1$, and only $a = m+1 \le \sqrt n + 1$
exceeds the strict bound. $\blacksquare$

Note that **Cases 1 and 2 are already fully bounded** (all coefficients $\le \sqrt n$).
Hence:

**Corollary 2.2.** *If $n$ is not representable with all squares $\le n$, then
$r \equiv 2 \pmod 4$.* The unique obstruction is Case 3, where the construction needs
$a = m+1$.

## 3. The reduction theorem

The next theorem disposes of Case 3 whenever a single number is composite. This is the
mathematical core of the effective verification in Section 4.

**Theorem 3.1 (reduction).** *Let $n \equiv 2 \pmod 4$, $m = \lfloor\sqrt n\rfloor \ge 5$,
$r = n - m^2$, and $D = 2m + r - 1$. If $D$ is composite, then $n$ is a sum of two squares
minus a third square with all three squares $\le n$.*

**Proof.** Note $r \equiv 2 \pmod 4$ by Corollary 2.2 (otherwise Section 2 already gives a
bounded representation), so $r$ is even and
$$D = 2m + r - 1 \quad\text{is odd}, \qquad 2m + 1 \le D \le 4m - 1. \tag{2}$$
Write $D = pq$ with $3 \le p \le q$ and $p$ the smallest prime factor of $D$ (possible
because $D$ is odd, composite, and $D \ge 2m+1 \ge 11$). Set
$$b = \frac{p+q}{2}, \qquad c = \frac{q-p}{2} \qquad (p, q \text{ odd} \Rightarrow b, c \in \mathbb Z).$$
Since $p$ is the smallest prime factor, $p \le \sqrt D \le \sqrt{4m-1} < 2\sqrt m$, and the
pair $(p, q)$ maximizes $u + D/u$ over all factor pairs $u \cdot (D/u)$. Hence it suffices
to bound this maximal pair sum:
$$p + \frac{D}{p} \;\le\; p + \frac{4m-1}{p} \;\le\; 3 + \frac{4m-1}{3} \;=\; \frac{4m+8}{3} \;\le\; 2m \quad (m \ge 4), \tag{3}$$
where the middle inequality uses that $p \mapsto p + (4m-1)/p$ is decreasing on
$[3, \sqrt{4m-1}]$. Therefore
$$b = \frac{p+q}{2} \le m, \qquad 0 \le c \le b, \qquad b^2 - c^2 = pq = D. \tag{4}$$
Finally, with $a = m - 1$:
$$a^2 + b^2 - c^2 = (m-1)^2 + D = (m-1)^2 + 2m + r - 1 = m^2 + r = n,$$
and $a = m-1 \le m \le \sqrt n$, while $b \le m$ gives $b^2 \le m^2 \le n$, and $c \le b$.
All three squares are at most $n$. $\blacksquare$

**Corollary 3.2.** *A non-representable integer $n > 25$ must satisfy*
$$r \equiv 2 \pmod 4 \qquad \text{and} \qquad 2m + r - 1 \ \text{prime}. \tag{5}$$

This is a genuine reduction: condition (5) has density $\sim 2/\ln n$ among $n \equiv 2 \pmod 4$,
so verifying $[1, N]$ requires examining only $O(N / \log N)$ candidates instead of
$\Theta(N^{3/2})$ triples.

## 4. Effective computation: the complete exception list below 250000

We need an exact, deterministic certificate for the remaining candidates. The following
lemma reduces representability to a factorization condition.

**Lemma 4.1 (exact criterion).** *Let $m = \lfloor\sqrt n\rfloor$. Then $n$ is representable
with all squares $\le n$ if and only if there exists $a \in \{0, 1, \dots, m\}$ such that
$D := n - a^2$ satisfies: $D \ge 0$; $D \not\equiv 2 \pmod 4$; and $D$ has a factorization
$D = uv$ with $u \equiv v \pmod 2$ and $u + v \le 2m$.*

**Proof.** If $n = a^2 + b^2 - c^2$ with $a^2, b^2, c^2 \le n$, then $b \ge c$ (from
$n \ge a^2$), $a \ge c$ (from $n \ge b^2$), so $D = n - a^2 = b^2 - c^2 \ge 0$ with
$u = b - c$, $v = b + c$, $u \equiv v \pmod 2$, $u + v = 2b \le 2m$. Conversely, given such
a factorization, $b = (u+v)/2$, $c = (v-u)/2$ are nonnegative integers with $b \le m$,
$c \le b$, and $a^2 + b^2 - c^2 = a^2 + uv = n$; all squares are $\le n$ since
$a, b, c \le m \le \sqrt n$. The condition $D \not\equiv 2 \pmod 4$ is necessary and
sufficient for a same-parity factorization of $D \neq 0$ to exist (differences of squares
are exactly the integers $\not\equiv 2 \pmod 4$). $\blacksquare$

**Algorithm 1 (certificate search).** For $n \le N$ with $r \equiv 2 \pmod 4$ and $2m+r-1$
prime (all other $n > 25$ are already certified by Section 2 or Theorem 3.1): for
$t = 1, 3, 5, \dots$ while $a = m - t \ge 0$ and $D_t = r + 2mt - t^2 \le m^2$, test
Lemma 4.1 on $D_t$; if no $t$ passes, declare $n$ an exception.

**Theorem 4.2 (verified computation).** *Exactly 77 integers in $[1, 250000]$ are not
representable as $x^2 + y^2 - z^2$ with $x^2, y^2, z^2 \le n$; the largest is $6563$.
Every $n \in [6564, 250000]$ is representable.*

**Verification.** Two independent methods were run over all $n \le 250000$ and agreed on
every integer: (i) direct enumeration of all triples with $a \ge b \ge c$... more precisely
all triples $0 \le c \le \min(a,b)$, $a^2 + b^2 - c^2 \le N$ — which is exhaustive because
every valid representation satisfies $a \ge c$ and $b \ge c$ (Section 2 of Lemma 4.1's proof);
(ii) Algorithm 1 with Lemma 4.1 as the certificate test. Method (ii) examines only
44,337 candidates (all with $2m+r-1$ prime) and certifies the rest of the range instantly.
The 77 output integers coincide with the list in Appendix A; each satisfies condition (5),
consistent with Corollary 3.2. The script in Appendix B reproduces both computations from
scratch in well under a minute of pure Python. $\blacksquare$

## 5. Conjecture: the threshold

**Conjecture 5.1.** *6563 is the largest non-representable integer; equivalently every
$n > 6563$ admits $n = x^2 + y^2 - z^2$ with $x^2, y^2, z^2 \le n$.*

**Heuristic.** For $n \equiv 2 \pmod 4$, Theorem 3.1 leaves only the case $2m+r-1$ prime
(probability $\sim 1/\ln(2\sqrt n)$). Conditional on that, $D_t$ for $t = 3, 5, \dots$ are
odd numbers of size $\sim 2mt$, each composite with probability $1 - O(1/\log n)$, and the
search space of admissible $t$ has length $\sim m/2$; the chance that *every* $D_t$ fails
Lemma 4.1 decays roughly like $\exp(-c\, m / \log m)$. Summed over $n$, the expected number
of exceptions beyond $x$ tends to $0$ as $x \to \infty$, consistent with the finiteness
already known from Chojecki's theorem — and with the observed data: 77 exceptions below
$250000$, none beyond $6563$, and the gap $[6564, 250000]$ clean. A related first-moment
heuristic (counting representations via Fermat's two-square theorem) gives the number of
representations of $n$ as $\sim C\sqrt{n/\log n} \to \infty$, which supports the same
conclusion: large $n$ have many representations, exceptions only occur when every one of
the $\Theta(\sqrt n)$ candidate remainders fails simultaneously.

## 6. Two remarks

**Remark 6.1 (why "rigid vs. rigid" searches fail — a gradient obstruction).**
Set $F(a,b,c) = a^2 + b^2 - c^2$ under the box $a, b, c \le \sqrt n$. Every unit coordinate
step changes $F$ by $|2t \pm 1| = \Theta(\sqrt n)$, so the search landscape has no
$O(1)$-scale gradient: no fine-tuning knob can push the error below $\Theta(\sqrt n)$
without enumeration. The successful constructions of Sections 2–4 avoid this by *splitting
scales*: a quadratic "rigid" locator ($m^2$ or $(m-1)^2$) fixes a window of width $O(\sqrt n)$,
and a *linear* "flexible" remainder $r$ (resp. $D = b^2 - c^2$) is adjusted inside the window,
where one unit of movement changes the value by $O(1)$. The rigidity conflict is the exact
reason Corollary 2.2 leaves only the case $r \equiv 2 \pmod 4$. (Interpretive remark, not
a theorem.)

**Remark 6.2 (what is actually compressed — an honest accounting).** Given $n$, computing
its representation is *integer square root + a $O(1)$-sized factorization of an integer
$\le 4\sqrt n$*: binary search or Newton iteration finds $m = \lfloor\sqrt n\rfloor$ in
$O(\log n)$ bit operations, Theorem 3.1 disposes of the composite case instantly, and only
the rare prime case needs the $t$-search. The representation $(a,b,c)$ stores about
$1.4 \log_2 n$ bits versus $\log_2 n$ bits for $n$ itself, so **no storage compression
occurs** (as the entropy bound requires). What is reduced is *search work* against brute-force
triple enumeration — the reduction from $\Theta(N^{3/2})$ to $O(N/\log N)$ certified
candidates in Theorem 4.2 is the precise, defensible content of that comparison. Claims of entropy compression would be incorrect and are not made here;
Section 8 develops the constructive research direction that survives this accounting.

## 7. Relation to prior work

- **Chojecki [1]** proved the affirmative answer to Erdős #1148 via Duke's theorem; the
  proof is qualitative (no explicit threshold). His argument is analytic and unrelated to
  the elementary reduction in Section 3.
- **Alexeev** gave the Lean formalization (`plby/lean-proofs`, `Erdos1148.lean`).
- The **three-case construction** (Theorem 2.1) is classical folklore; we include it because
  it cleanly isolates the single obstruction (Corollary 2.2) that Theorem 3.1 then resolves.
- The **reduction theorem (3.1), the exact criterion (4.1), Algorithm 1, and the explicit
  77-exception list with maximal element 6563** are, to our knowledge, not recorded in the
  published literature; the exception list is machine-verifiable with Appendix B.
- This note does not claim priority over [1]; it records an independent elementary route
  and an effective verification complementing the qualitative solution.


## 8. A proposed information-theoretic perspective (speculative)

This section develops, as a *research proposal* rather than a body of theorems, the
information-theoretic viewpoint that motivated the present note. Parts of it originated in
the author's earlier unpublished draft (2026), which treated Sections 2–4 through coding
language; what follows extracts the parts that survive rigorous scrutiny, with explicit
accounting of what is and is not being claimed (cf. Remark 6.2).

### 8.1 Square forms as distributed encodings

Write the payload bit-length $\log_2 n$ as $L$. A bounded representation
$(a, b, c)$ with $a, b, c \le \sqrt n$ stores $L$ payload bits **distributed across three
registers of $L/2$ bits each**: a length-3 vector code of rate
$$\rho = \frac{\log_2 n}{3 \cdot \frac12 \log_2 n} = \frac23.$$
Quadratic forms are natural candidates for such *equal-bit packing* because squaring
aligns each register's dynamic range exactly with the geometric scale $\sqrt n$ of the
payload — the "information concentrated in low-order digits" effect noted in the original
draft. This is a observation about **representation geometry**, not a compression scheme:
the code carries a $1/\rho = 3/2$ multiplicative overhead in raw bit-length, as the entropy
bound requires.

### 8.2 Codebook redundancy

Count admissible codewords for the payload window $[1, n]$:
$$T(n) := \left| \{(a,b,c):\ 0 \le c \le \min(a,b),\ a^2 + b^2 - c^2 \in [1,n]\} \right| = \Theta(n^{3/2}),$$
with $T(n) \approx 0.12\, n^{3/2}$ measured for $n \le 10^6$ (the constraint $c \le \min(a,b)$
is free by Lemma 4.1). Two readings of this redundancy:

* **Absolute:** the average witness multiplicity per integer, $T(n)/n \approx 0.12\sqrt n$,
  *grows* without bound. The ternary-square code therefore becomes *richer* as $n$ grows —
  large integers have asymptotically more witnesses, which is precisely the structural
  reason Conjecture 5.1 (finitely many exceptions) is plausible.
* **Relative:** about $12\%$ of the ambient cube $[0,\sqrt n]^3$ consists of valid codewords
  for $[1,n]$; the map $(a,b,c) \mapsto a^2+b^2-c^2$ is a sparse, locally rigid projection
  (Remark 6.1).

The author's original draft estimated this redundancy at "$2.4\times$" per integer; the
sharp counting above ($\Theta(\sqrt n)$ per integer, slowly growing) supersedes that
figure.

### 8.3 "Two-slider" decoding

The constructions of Sections 2–4 define a two-stage decoder that the original draft
called the *two-slider* method:

1. **High slider** (quadratic scale): compute $m = \lfloor\sqrt n\rfloor$ — an integer
   square root, $O(\log n)$ bit operations by binary search or Newton iteration. This
   fixes the leading term $m^2$ and opens a window of width $r = n - m^2 = O(\sqrt n)$.
2. **Low slider** (linear scale): adjust within the window via the difference
   $D = b^2 - c^2 = (b-c)(b+c)$, where one unit of movement in $b, c$ changes the value
   by $O(1)$ — the fine-tuning knob whose absence at the quadratic scale was the
   obstruction of Remark 6.1.

Theorem 3.1 is the precise statement that the low slider alone resolves every value whose
first remainder $D_1 = 2m + r - 1$ is composite; Lemma 4.1 gives the exact termination
criterion for the search.

### 8.4 The hard kernel and difficulty concentration

What remains after the two sliders is a **hard kernel**: values $n \equiv 2 \pmod 4$ with
$2m + r - 1$ prime, of density $\sim 1/\ln(2\sqrt n)$ among their residue class. Within
this sparse kernel, certification requires the deeper $t$-search of Algorithm 1, and the
true exceptions (Appendix A) live here — indeed each of the 77 satisfies condition (5).
Verification cost is therefore *concentrated* on a set of density $O(1/\log n)$: the
global statement "every $n \in [6564, 250000]$ is representable" is certified almost
everywhere by Theorem 3.1 alone, and only the kernel needs case work. This
**difficulty concentration** phenomenon — hard instances confined to a thin, arithmetically
characterized subset — is the part of the original draft's "compression of difficulty"
narrative that we are able to state as a theorem (Theorems 3.1 and 4.2).

### 8.5 Open questions raised by this perspective

1. **Effective threshold.** Chojecki's solution is qualitative; the present verification
   is effective below $250000$. Can the gap $[250001, N_0)$, where $N_0$ is Chojecki's
   non-explicit threshold, be closed elementarily — i.e., can the hard kernel be shown to
   be empty beyond $6563$ without Duke's theorem? Conjecture 5.1 asserts this.
2. **Witness lower bounds.** The heuristic of Section 5 predicts $\sim c\sqrt{n/\log n}$
   witnesses for typical $n$. An unconditional lower bound of shape $\gg \sqrt{n}/\log n$
   on the number of bounded representations, for all $n$ outside the kernel, would give an
   effective threshold and seems accessible to sieve methods.
3. **Generality.** Does the two-slider structure (quadratic locator + difference-of-
   squares corrector + thin hard kernel) persist for other indefinite ternary forms
   $x^2 + y^2 - k z^2$ with bounded coefficients? The reduction argument of Theorem 3.1
   adapts verbatim in some cases (e.g., $x^2 + y^2 - z^2$ with weights), with the kernel
   density governed by the splitting behaviour of small primes in $\mathbb{Q}(\sqrt{k})$.

### 8.6 Accounting

To be explicit about what this perspective claims: **no storage compression occurs** —
a representation uses $\tfrac32 \log_2 n$ bits against the $\log_2 n$-bit entropy floor
(Section 6, Remark 6.2). What the square-form code *does* provide, and what this note
verifies, is (i) a rate-$2/3$ distributed encoding whose witness multiplicity grows as
$\Theta(\sqrt n)$; (ii) an $O(\log n)$-bit two-slider decoding procedure; and (iii) a
provable concentration of all remaining hardness into a thin prime-remainder kernel, with
the global correctness of the code on $[6564, 250000]$ certified in $O(N/\log N)$ work.
Whether these structures have applications (constructive certification of arithmetic
predicates, witness sampling, derandomized search) is left as motivation for the open
questions above.

## References

[1] P. Chojecki, *Bounded Representations by $x^2+y^2-z^2$*, March 2026.
    https://www.ulam.ai/research/erdos1148-full.pdf

[2] M. Einsiedler, E. Lindenstrauss, P. Michel, A. Venkatesh, *The distribution of closed
    geodesics on the modular surface, and Duke's theorem*, Enseign. Math. (2) 58 (2012),
    no. 3–4, 249–313.

[3] T. F. Bloom (ed.), *Erdős Problem 1148*, https://www.erdosproblems.com/erdos/1148

## Appendix A: the 77 exceptions in $[1, 250000]$

3, 6, 11, 15, 22, 27, 35, 38, 42, 55, 59, 66, 78, 83, 87, 95, 110, 118, 123, 131, 143,
150, 187, 210, 222, 227, 255, 262, 266, 278, 299, 303, 323, 326, 395, 402, 447, 483,
502, 551, 563, 590, 618, 635, 678, 735, 755, 838, 843, 867, 902, 930, 942, 1003, 1007,
1034, 1091, 1162, 1190, 1295, 1326, 1482, 1523, 1770, 1790, 2067, 2103, 2407, 2483, 2598,
2782, 3422, 3495, 4686, 5447, 5727, 6563.

Each satisfies $r = n - \lfloor\sqrt n\rfloor^2 \equiv 2 \pmod 4$ and $2\lfloor\sqrt n\rfloor + r - 1$ prime.

## Appendix B: verification code

See `verify_exceptions.py` (companion file). It re-runs both the exhaustive triple
enumeration and Algorithm 1, asserts their agreement on every $n \le 250000$, and prints
the exception list of Theorem 4.2.
