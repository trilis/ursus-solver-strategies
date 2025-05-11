## Ursus Solver Strategies

**Heuristic Strategies for Term Reduction in the Domain of Formal Verification**

The interactive theorem prover Coq is widely used in many works on formal software verification. However, Coq’s computational mechanisms, which are essential for formal verification, often lack the performance needed to solve practical problems. In the Ursus framework, designed for verifying smart contracts in Coq, a key challenge is the efficient symbolic evaluation of function results. This work is dedicated to optimizing that process. Several evaluation strategies have been developed, based on call-by-value and call-by-need approaches, employing decomposition techniques and heuristically taking into account structural patterns in the input data, including heuristics related to data types and graph-based characteristics of the problem. The developed strategies are compared against one another on both synthetic and real-world data, leading to the selection of several strategies that demonstrated the best results for practical use.

### Project structure

* `src/CommonTactics.v` — main file, strategies written in Ltac
* `src/Simple/Simple.v`, `src/Recursion/Recursion.v`, `src/If/If.v`, `src/IfAndRecursion/IfAndRecursion.v` — test programs for benchmarking 
* `src/Simple/Proofs`, `src/Recursion/Proofs`, `src/If/Proofs`, `src/IfAndRecursion/Proofs` — launching strategies on benchmarks
* `plots/` — tools to visualize benchmarking results

### Building

```
./run_experiments.sh
```

Can only be ran after installing Ursus internal libraries. They can be provided per request pre-installed in Docker container. Please change `JOBS` variable in `run_experiments.sh` to fit your computing configuration.