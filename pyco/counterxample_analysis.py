'''
This module implements the functions necessary to learn from the verifier whether there
exist a port swap that can satisfy the spec.
If so, a counterexample is generated and analyzed to infer the correct connections.

Author: Antonio Iannopollo
'''

from pyco import LOG


def counterexample_analyzer()