# Concrete Counterexample Check

This folder gives a small computational check of the counterexample

```math
\mathcal F=\{K_{1,2},\,2K_2\}.
```

The script `bruteforce_counterexample.py` enumerates every simple graph on
`n` labeled vertices for small `n` and computes:

- `ex(n, K_{1,2})`
- `ex(n, 2K_2)`
- `ex(n; {K_{1,2}, 2K_2})`

Run it from the repository root:

```sh
python3 examples/bruteforce_counterexample.py
```

Expected output:

```text
n  ex(K1,2)  witness            ex(2K2)  witness                  ex(F)  witness
0  0         []                 0        []                       0      []
1  0         []                 0        []                       0      []
2  1         [(0, 1)]           1        [(0, 1)]                 1      [(0, 1)]
3  1         [(0, 1)]           3        [(0, 1), (0, 2), (1, 2)] 1      [(0, 1)]
4  2         [(0, 3), (1, 2)]   3        [(0, 1), (0, 2), (0, 3)] 1      [(0, 1)]
5  2         [(0, 3), (1, 2)]   4        [(0, 1), (0, 2), (0, 3), (0, 4)] 1      [(0, 1)]
6  3         [(0, 5), (1, 4), (2, 3)] 5        [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5)] 1      [(0, 1)]
```

For instance, at `n = 4`:

- forbidding only `K_{1,2}` allows a matching with `2` edges;
- forbidding only `2K_2` allows a star with `3` edges;
- forbidding both allows only `1` edge.

This computation is only an illustration. The general statement for all `n`
is proved in the Lean formalization and in the proof in the root README.
