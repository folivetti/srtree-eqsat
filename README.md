# srtree-eqsat

A CLI tool to simplify Symbolic Regression expressions using Equality Saturation.
The simplification has the main objective of reparameterizing the expression with a smaller number of parameters.

## Instalation

First you need to install Haskell stack (https://docs.haskellstack.org/en/stable/)[https://docs.haskellstack.org/en/stable/], and then you can run:

```bash
stack install
```

Optionally, you can download the release binaries from this repository (https://github.com/folivetti/srtree-eqsat/releases).

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
