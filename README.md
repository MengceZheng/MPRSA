# Improved Factoring Attacks on Multi-prime RSA with Small Prime Difference

## Introduction

This is a Python implementation of lattice-based factoring attack proposed in **Improved Factoring Attacks on Multi-prime RSA with Small Prime Difference**[^MPRSA] (for $N=p_1p_2p_3$ with $r=3$ using the optimized method).

## Requirements

- [**SageMath**](https://www.sagemath.org/) 9.5 with Python 3.10

You can check your SageMath Python version using the following command:

```commandline
$ sage -python --version
Python 3.10.12
```

Note: If your SageMath Python version is older than 3.9.0, some features in given scripts might not work.

## Usage

The standard way to run the attack with the specific parameters requires passing them as command line arguments `sage -python attack.py <prime_bit_length> <gamma> <s>`. For instance, to run the attack with $\ell=64$, $\gamma=0.105$, and $s=15$, please run `sage -python attack.py 64 0.105 15`:

```commandline
MPRSA$ sage -python attack.py 64 0.105 15
The parameters:
N = 3406532389759339108982571425153526701119279049168932006019
r = 3
p = 15046569918049546240
Found primes:
[15046569918049100539, 15046569918049503139, 15046569918050149139]
The attack costs 21.663 seconds...
```

For instance, to run the attack with $\ell=32$, $\delta=0.11$, and $s=18$, please run `sage -python attack.py 32 0.11 18`:

```commandline
MPRSA$ sage -python attack.py 32 0.11 18
The parameters:
N = 42790195655015864954176742677
r = 3
p = 3497690876
Found primes:
[3497690527, 3497690543, 3497691557]
The attack costs 45.088 seconds...
```

## Notes

All the details of the numerical attack experiments are recorded in the `attack.log` file. A more efficient lattice reduction algorithm [flatter](https://github.com/keeganryan/flatter) is used and `USE_FLATTER = True`.

[^MPRSA]: Zheng M., Kunihiro N., Hu H., "Improved Factoring Attacks on Multi-prime RSA with Small Prime Difference" | [ePrint](https://eprint.iacr.org/2015/1137)
