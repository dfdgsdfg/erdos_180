# Erdős Problem 180

## Problem
https://www.erdosproblems.com/forum/thread/180

Let $F$ be a finite set of finite graphs. Let

```math
\mathrm{ex}(n;F)
```

denote the maximum number of edges in a graph on $n$ vertices which contains
no member of $F$ as a subgraph. It is immediate that

```math
\mathrm{ex}(n;F)\le \mathrm{ex}(n;G)
```

for every $G\in F$.

Is it true that, for every finite family $F$, there exists $G\in F$ such that

```math
\mathrm{ex}(n;G)\ll_F \mathrm{ex}(n;F)?
```

## Answer
https://chatgpt.com/share/6a0fe2fe-1ba4-83a6-befe-76c6cb34aaf3

No. The proposed statement is false.

Related context:

[1] Y. Wigderson, *The Erdős-Simonovits compactness conjecture needs more
assumptions*.
<https://ywigderson.math.ethz.ch/math/static/Compactness.pdf>

[2] P. Erdős and M. Simonovits, *Compactness results in extremal graph theory*,
Combinatorica 2 (1982), 275-288.
DOI/Springer: <https://link.springer.com/article/10.1007/BF02579234>
PDF: <https://www.renyi.hu/~p_erdos/1982-02.pdf>

[3] V. Chvátal and D. Hanson, *Degrees and matchings*, Journal of Combinatorial
Theory, Series B 20 (1976), 128-138.
DOI: <https://doi.org/10.1016/0095-8956(76)90004-6>
ScienceDirect: <https://www.sciencedirect.com/science/article/pii/0095895676900046>

[4] D. Conlon, E. Mulrenin, and C. Pohoata, *Two counterexamples to a conjecture
about even cycles*, arXiv:2603.24515.
<https://arxiv.org/abs/2603.24515>

## Proof

Let

```math
\mathcal F=\{K_{1,2},\,2K_2\},
```

where $K_{1,2}$ is the path of length $2$, and $2K_2$ is a matching of two
disjoint edges.

First,

```math
\mathrm{ex}(n,K_{1,2})=\left\lfloor \frac n2\right\rfloor .
```

Indeed, a graph is $K_{1,2}$-free if and only if every vertex has degree at
most $1$. Hence such a graph is a matching, and the largest matching on $n$
vertices has size $\lfloor n/2\rfloor$.

Next, for $n\ge 4$,

```math
\mathrm{ex}(n,2K_2)=n-1.
```

The lower bound is given by the star $K_{1,n-1}$, which has $n-1$ edges and
contains no two disjoint edges.

For the upper bound, suppose $G$ is $2K_2$-free. Then every two edges of $G$
intersect. If $G$ has two incident edges $ab$ and $ac$, then every other edge
must intersect both $ab$ and $ac$. Hence every other edge either contains $a$,
or is the edge $bc$. If no edge $bc$ occurs, then all edges are contained in a
star centered at $a$. If $bc$ occurs, then no edge $ax$ with
$x\notin\{b,c\}$ can occur, since it would be disjoint from $bc$. Thus all
edges lie inside the triangle on $\{a,b,c\}$. Therefore

```math
e(G)\le \max\{n-1,3\}=n-1
```

for $n\ge 4$. Thus

```math
\mathrm{ex}(n,2K_2)=n-1.
```

Now forbid both graphs simultaneously. If $G$ is $K_{1,2}$-free, then $G$ is a
matching. If $G$ is also $2K_2$-free, then this matching has size at most $1$.
Hence, for $n\ge 2$,

```math
\mathrm{ex}(n;\mathcal F)=1.
```

Consequently,

```math
\mathrm{ex}(n,K_{1,2})=\Theta(n),
\qquad
\mathrm{ex}(n,2K_2)=\Theta(n),
```

but

```math
\mathrm{ex}(n;\mathcal F)=\Theta(1).
```

Therefore, for every $G\in\mathcal F$,

```math
\mathrm{ex}(n;G)\not\ll_{\mathcal F}\mathrm{ex}(n;\mathcal F).
```

Indeed, $\mathrm{ex}(n;G)$ grows linearly in $n$, while
$\mathrm{ex}(n;\mathcal F)$ is bounded by a constant. Thus there is no
$G\in\mathcal F$ such that

```math
\mathrm{ex}(n;G)\ll_{\mathcal F}\mathrm{ex}(n;\mathcal F).
```

Hence the proposed statement is false.

The only small-$n$ qualification is that

```math
\mathrm{ex}(n;\mathcal F)=1
```

is asserted for $n\ge 2$; for $n=0,1$, the value is $0$. This does not affect
the asymptotic conclusion.

## Lean formalization

The Lean proof is contained in `E180/Basic.lean`. It formalizes the same
counterexample using `SimpleGraph`, the finite vertex set `Fin n`, non-induced
subgraph-containment predicates for $K_{1,2}$ and $2K_2$, and the extremal
maximum over all graphs on `Fin n`.

## Concrete examples

The `examples/` directory contains a small dependency-free brute-force check
for `n <= 6`. It enumerates all simple graphs on `n` labeled vertices and
prints concrete extremal witnesses for the same counterexample.
