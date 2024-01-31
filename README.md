PyCo
====
#### a Python library for Contract-based synthesis


This library provides tools to perform synthesis of
*Linear Temporal Logic (LTL)-based Assume/Guarantee (A/G)contracts*.
Given a contract describing the system specification,
PyCo is able to choose other contracts from a library,
and connect them together such that their composition
is a refinement of the specification.

## Prerequisites
To use PyCo, you need to first install [pycolite](https://github.com/ianno/pycolite),
which provides some low level primitives to manipulate contracts.

## Getting Started
This project can be installed as a python package,
and can be used by importing it in your python source files.

### Installing
To install the library, go to the root folder of the project (AFTER having installed [pycolite](https://github.com/ianno/pycolite)) and, from a command line, run

```bash
pip install -e .
```

This last command will install all the required python dependencies.

### Testing
To make sure the installation has been successful,
you can run some tests by running from a command line,
always in the project root folder:

```bash
python -m pytest pyco/tests/test_synthesis.py
```
After executing the last command, you should get a message saying that all the tests were passed.

## Running PyCo
You can integrate PyCo in your projects as a python package.
Check out the examples in `pyco/examples` and `pyco/tests`.

A typical usage example of PyCo can be found in the `design_example.py` file.
The library used in the example is defined in
`pyco/examples/example_eps_facs.py`.

To execute it, run from a command line:

```bash
python design_example.py
```

After synthesis, the tool generates a PDF file with the solution representation, and a text file with extension `.pyco`,
containing the same information in ASCII friendly format.

### SCP 24
If you are looking for the code used for our SCP submission, look [here](https://github.com/ianno/pyco/tree/scp24). A reproducibility package is being built but that brunch contains code and data, and that should be sufficient by itself.
That code in that branch is substantially different than the rest of this repo, and some commands referenced in this README might not work.

### FACS 2016
This work has been developed as a supporting tool for a work presented at [Formal Aspects of Component Software - The 13th International Conference, Besançon, France - FACS 2016](http://events.femto-st.fr/facs2016/).

To run the experiments used in the paper, see and run the `pyco_facs.py` file.

For info on how to execute `pyco_facs.py`, use the command:

```bash
python pyco_facs.py --help
```

To take a look a the library used for FACS 2016,
check `pyco/examples/example_eps_facs.py` and
`pyco/tests/test_eps_facs.py`.
All the tests have been written to be run as a py.test test suite.

## Citations
Please **acknowledge** the use of PyCo by citing this Github repository and the article:

Iannopollo A., Tripakis S., Sangiovanni-Vincentelli A. (2017) Constrained Synthesis from Component Libraries. In: Kouchnarenko O., Khosravi R. (eds) Formal Aspects of Component Software. FACS 2016. Lecture Notes in Computer Science, vol 10231. Springer, Cham

or, in Bibtex format:

```bibtex
@Inbook{Iannopollo2017,
author="Iannopollo, Antonio
and Tripakis, Stavros
and Sangiovanni-Vincentelli, Alberto",
editor="Kouchnarenko, Olga
and Khosravi, Ramtin",
title="Constrained Synthesis from Component Libraries",
bookTitle="Formal Aspects of Component Software: 13th International Conference, FACS 2016, Besan{\c{c}}on, France, October 19-21, 2016, Revised Selected Papers",
year="2017",
publisher="Springer International Publishing",
address="Cham",
pages="92--110",
isbn="978-3-319-57666-4",
doi="10.1007/978-3-319-57666-4_7",
url="http://dx.doi.org/10.1007/978-3-319-57666-4_7"
}
```

## Authors
* [Antonio Iannopollo](https://people.eecs.berkeley.edu/~antonio/)

## License
This project is released under the GPLv3 license.
For more information, see [LICENSE](https://github.com/ianno/pycolite/blob/master/LICENSE).
