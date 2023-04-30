# srtree-eqsat

A CLI tool to simplify Symbolic Regression expressions using Equality Saturation.
The simplification has the main objective of reparameterizing the expression with a smaller number of parameters.

**NOTE: ** this tool will be discontinued and the simplification cli can be performed using https://github.com/folivetti/pandoc-symreg

## Instalation

You can download the release binaries from this repository (https://github.com/folivetti/srtree-eqsat/releases).

## Command line help:

```bash
srtree-eqsat -h
```

## Example usage:

Parse the Heuristic Lab expressions in `test/example_hl` file using the named variables `alpha,beta,theta` as $x0, x1, x2$, respectivelly.

```bash
srtree-eqsat -f hl -i test/example_hl -v "alpha,beta,theta"
```

By default the fitted expressions will be printed in stdout, but you can specify the output files with the `-o` flag.
