# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulas to use only specific sets of
operators."""

from propositions.syntax import *
from propositions.semantics import *

def to_not_and_or(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'``, ``'&'``, and ``'|'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'``, ``'&'``, and
        ``'|'``.
    """
    # Task 3.5
    if is_variable(formula.root):
        return Formula(formula.root)

    v = next(iter(formula.variables()), 'p')

    if is_constant(formula.root):
        if formula.root == 'T':
            return Formula('|', Formula(v), Formula('~', Formula(v)))
        return Formula('&', Formula(v), Formula('~', Formula(v)))

    if is_unary(formula.root):
        return Formula('~', to_not_and_or(formula.first))

    first = to_not_and_or(formula.first)
    second = to_not_and_or(formula.second)

    if formula.root == '&':
        return Formula('&', first, second)
    if formula.root == '|':
        return Formula('|', first, second)
    if formula.root == '->':
        return Formula('|', Formula('~', first), second)
    if formula.root == '+':
        left = Formula('&', first, Formula('~', second))
        right = Formula('&', Formula('~', first), second)
        return Formula('|', left, right)
    if formula.root == '<->':
        left = Formula('&', first, second)
        right = Formula('&', Formula('~', first), Formula('~', second))
        return Formula('|', left, right)
    if formula.root == '-&':
        return Formula('~', Formula('&', first, second))
    assert formula.root == '-|'
    return Formula('~', Formula('|', first, second))


def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'`` and ``'&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'`` and ``'&'``.
    """
    # Task 3.6a
    if is_variable(formula.root):
        return Formula(formula.root)

    v = next(iter(formula.variables()), 'p')

    if is_constant(formula.root):
        if formula.root == 'T':
            return Formula('~', Formula('&', Formula(v), Formula('~', Formula(v))))
        return Formula('&', Formula(v), Formula('~', Formula(v)))

    if is_unary(formula.root):
        return Formula('~', to_not_and(formula.first))

    first = to_not_and(formula.first)
    second = to_not_and(formula.second)

    if formula.root == '&':
        return Formula('&', first, second)
    if formula.root == '|':
        return Formula('~', Formula('&', Formula('~', first), Formula('~', second)))
    if formula.root == '->':
        return Formula('~', Formula('&', first, Formula('~', second)))
    if formula.root == '+':
        a_or_b = Formula('~', Formula('&', Formula('~', first), Formula('~', second)))
        a_and_b = Formula('&', first, second)
        return Formula('&', a_or_b, Formula('~', a_and_b))
    if formula.root == '<->':
        a_and_b = Formula('&', first, second)
        na_and_nb = Formula('&', Formula('~', first), Formula('~', second))
        return Formula('~', Formula('&', Formula('~', a_and_b), Formula('~', na_and_nb)))
    if formula.root == '-&':
        return Formula('~', Formula('&', first, second))
    assert formula.root == '-|'
    return Formula('&', Formula('~', first), Formula('~', second))


def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'-&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'-&'``.
    """
    # Task 3.6b
    def nand(a: Formula, b: Formula) -> Formula:
        return Formula('-&', a, b)

    if is_variable(formula.root):
        return Formula(formula.root)

    v = next(iter(formula.variables()), 'p')
    t = nand(Formula(v), nand(Formula(v), Formula(v)))
    f = nand(t, t)

    if is_constant(formula.root):
        if formula.root == 'T':
            return t
        return f

    if is_unary(formula.root):
        x = to_nand(formula.first)
        return nand(x, x)

    first = to_nand(formula.first)
    second = to_nand(formula.second)

    if formula.root == '-&':
        return nand(first, second)

    if formula.root == '&':
        x = nand(first, second)
        return nand(x, x)

    if formula.root == '|':
        na = nand(first, first)
        nb = nand(second, second)
        return nand(na, nb)

    if formula.root == '->':
        nb = nand(second, second)
        return nand(first, nb)

    if formula.root == '-|':
        na = nand(first, first)
        nb = nand(second, second)
        a_or_b = nand(na, nb)
        return nand(a_or_b, a_or_b)

    if formula.root == '+':
        na = nand(first, first)
        nb = nand(second, second)
        a_or_b = nand(na, nb)
        a_and_b = nand(nand(first, second), nand(first, second))
        not_a_and_b = nand(a_and_b, a_and_b)
        x = nand(a_or_b, not_a_and_b)
        return nand(x, x)

    assert formula.root == '<->'
    na = nand(first, first)
    nb = nand(second, second)
    a_or_b = nand(na, nb)
    a_and_b = nand(nand(first, second), nand(first, second))
    not_a_and_b = nand(a_and_b, a_and_b)
    x = nand(a_or_b, not_a_and_b)
    return x


def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'~'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'~'``.
    """
    # Task 3.6c
    def make_or(a: Formula, b: Formula) -> Formula:
        return Formula('->', Formula('~', a), b)

    def make_and(a: Formula, b: Formula) -> Formula:
        return Formula('~', Formula('->', a, Formula('~', b)))

    if is_variable(formula.root):
        return Formula(formula.root)

    v = next(iter(formula.variables()), 'p')
    t = Formula('->', Formula(v), Formula(v))

    if is_constant(formula.root):
        if formula.root == 'T':
            return t
        return Formula('~', t)

    if is_unary(formula.root):
        return Formula('~', to_implies_not(formula.first))

    first = to_implies_not(formula.first)
    second = to_implies_not(formula.second)

    if formula.root == '->':
        return Formula('->', first, second)

    if formula.root == '|':
        return make_or(first, second)

    if formula.root == '&':
        return make_and(first, second)

    if formula.root == '-&':
        return Formula('~', make_and(first, second))

    if formula.root == '-|':
        return Formula('~', make_or(first, second))

    if formula.root == '<->':
        return make_and(Formula('->', first, second), Formula('->', second, first))

    assert formula.root == '+'
    a_or_b = make_or(first, second)
    a_and_b = make_and(first, second)
    return make_and(a_or_b, Formula('~', a_and_b))


def to_implies_false(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'F'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'F'``.
    """
    # Task 3.6d
    def make_not(a: Formula) -> Formula:
        return Formula('->', a, Formula('F'))

    def make_or(a: Formula, b: Formula) -> Formula:
        return Formula('->', make_not(a), b)

    def make_and(a: Formula, b: Formula) -> Formula:
        return make_not(Formula('->', a, make_not(b)))

    if is_variable(formula.root):
        return Formula(formula.root)

    t = Formula('->', Formula('F'), Formula('F'))

    if is_constant(formula.root):
        if formula.root == 'T':
            return t
        return Formula('F')

    if is_unary(formula.root):
        return make_not(to_implies_false(formula.first))

    first = to_implies_false(formula.first)
    second = to_implies_false(formula.second)

    if formula.root == '->':
        return Formula('->', first, second)

    if formula.root == '|':
        return make_or(first, second)

    if formula.root == '&':
        return make_and(first, second)

    if formula.root == '-&':
        return make_not(make_and(first, second))

    if formula.root == '-|':
        return make_not(make_or(first, second))

    if formula.root == '<->':
        return make_and(Formula('->', first, second), Formula('->', second, first))

    assert formula.root == '+'
    a_or_b = make_or(first, second)
    a_and_b = make_and(first, second)
    return make_and(a_or_b, make_not(a_and_b))

