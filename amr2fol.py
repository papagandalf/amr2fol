#!/usr/bin/python2.7
# -*- coding: utf-8 -*-
"""
AMR transformer to first order logic expressions
implementation of Bos, J. Expressive Power of Abstract Meaning Representations, ACL, 2016.
"""

import penman
from nltk.sem.logic import Expression


def strip_lambdas(expression):
    expression_str = str(expression)
    ret = []
    in_lambda = False
    for char in expression_str:
        if char == "\\":
            in_lambda = True
        elif in_lambda:
            if char == ".":
                in_lambda = False
        else:
            ret.append(char)
    return Expression.fromstring("".join(ret))

def eliminate_t(expression):
    expression_str = str(expression)
    pattern = " & T("
    index = expression_str.find(pattern)
    if index == -1:
        return expression
    expression_str = expression_str[:index] + expression_str[index+len(pattern)+2:]
    return Expression.fromstring(expression_str)

def create_graph(triples, top):
    assert top is not None
    g = penman.AMRCodec().triples_to_graph(triples, top=top)
    return g

def get_variable_concept(variable, amr_graph):
    concept = amr_graph.attributes(source=variable, relation="instance")
    assert len(concept) == 1
    return concept[0].target

def get_outgoing_relations(variable, amr_graph):
    # Filters out variable's concept and polarity
    return [t for t in amr_graph._triples if t.source == variable and t.relation not in ["instance", "polarity"]]

def is_projective(variable, amr_graph):
    assert variable in amr_graph.variables()
    return len(amr_graph.triples(target=variable)) > 1

def is_negative(variable, amr_graph):
    polarity = len(amr_graph.attributes(source=variable, relation="polarity", target="-"))
    assert polarity <= 1
    return polarity == 1

def normalize_predicate_name(predicate_name):
    predicate_name = predicate_name.strip().replace("-", "_")
    if predicate_name in ["and", "or", "implies", "iff", "some", "exists", "exist", "all", "forall", "not"]:
        predicate_name = predicate_name.upper()
    if len(predicate_name) == 1:
        predicate_name = "_{}_".format(predicate_name)
    return predicate_name

def normalize_constant(constant):
    return constant.replace(".", "_DOT_").replace(" ", "_SPACE_").replace("-", "_")

def amr2fol(amr, debug=False):
    amr_graph = penman.loads(amr, cls=penman.AMRCodec)
    assert len(amr_graph) == 1, "More than one AMR supplied"
    amr_graph = amr_graph[0]
    set_graph_root(amr_graph)
    assertive_part = lambda_amr_assertive(amr_graph, "\u.T") # TODO: must u here be unique?
    assertive_logic = Expression.fromstring(assertive_part).simplify()
    projective_part = lambda_amr_projective(amr_graph)
    projective_logic = Expression.fromstring(projective_part).simplify()
    final_logic = (projective_logic(assertive_logic)).simplify()
    final_logic = eliminate_t(strip_lambdas(final_logic)).simplify()
    if debug:
        print "assertive logic: {}".format(assertive_part)
        print "assertive logic (simplified): {}".format(assertive_logic)
        print "prjective logic: {}".format(projective_part)
        print "projective logic (simplified): {}".format(projective_logic)
        print "final logic (simplified, stripped lambdas, eliminate T): {}".format(final_logic)
    assert len(final_logic.free()) == 0
    return final_logic

def lambda_amr_assertive(amr_graph, phi, ignore_projective=False):
    top = amr_graph.top

    if not ignore_projective and is_projective(top, amr_graph):
        return "{0}({1})".format(phi, top)

    concept = get_variable_concept(top, amr_graph)
    negative = is_negative(top, amr_graph)
    relations = get_outgoing_relations(top, amr_graph)
    if len(relations) == 0:
        lambda_string = ""
        if negative:
            lambda_string = "-"
        lambda_string += "exists {0}.({1}({0}) & {2}({0}))".format(top, normalize_predicate_name(concept), phi)
        return lambda_string

    lambda_string = ""
    if negative:
        lambda_string = "-"
    lambda_string += "exists {0}.({1}({0})".format(top, normalize_predicate_name(concept))

    future_projective_variables = set()
    for t in relations:
        assert t.source == top
        relation = t.relation
        other = t.target
        if other not in amr_graph.variables():
            # other is a constant
            lambda_string += " & {0}({1}, {2})".format(relation, top, normalize_constant(other))
        else:
            if is_projective(other, amr_graph):
                future_projective_variables.add(other)
            part_lambda_string = lambda_amr_assertive(create_graph(amr_graph.triples(), other),
                                                      "\y.{0}({1}, y)".format(relation, top))
            lambda_string += " & {0}".format(part_lambda_string)

    lambda_string += " & {0}({1}))".format(phi, top)

    if len(future_projective_variables) > 0:
        lambda_string = "\{0}.({1})".format(" ".join(list(future_projective_variables)), lambda_string)
    return lambda_string

def lambda_amr_projective(amr_graph):    
    top = amr_graph.top
    relations = get_outgoing_relations(top, amr_graph)
    projective = is_projective(top, amr_graph)

    if len(relations) == 0:
        if projective:
            part_lambda_string = lambda_amr_assertive(amr_graph, "(\{0}.P1)".format(top), ignore_projective=True)
            return "(\P1.({0}))".format(part_lambda_string)
        return "(\P1.P1)"

    if projective:
        return "(\P1.({0}))".format(lambda_amr_assertive(amr_graph, "(\{0}.P1)".format(top), ignore_projective=True))

    lambda_string = "\P2."
    for t in reversed(relations):
        assert t.source == top
        relation = t.relation
        other = t.target
        if other not in amr_graph.variables():
            # other is a constant
            part_lambda_string = "(\P1.P1)"
        else:
            part_lambda_string = lambda_amr_projective(create_graph(amr_graph.triples(), other))
        lambda_string += "{0}(".format(part_lambda_string)

    lambda_string += "(P2)"
    lambda_string += ")"*len(relations)
    return lambda_string

def set_graph_root(amr_graph):
    variables = amr_graph.variables()
    triples = amr_graph.triples()
    indegrees = { var: 0 for var in variables }
    for t in triples:
        target = t.target
        if target not in variables:
            # target is a constant
            continue
        indegrees[target] += 1
    root = [node for node in indegrees if indegrees[node] == 0]
    assert len(root) == 1, "Found multiple roots: {}".format(" ".join(root))
    amr_graph.top = root[0]


if __name__ == "__main__":
    import sys
    if len(sys.argv) < 2:
        print "Usage: python {0} amr-filepath".format(sys.argv[0])
        sys.exit(1)
    graphs = penman.load(sys.argv[1], cls=penman.AMRCodec)
    for g in graphs:
        set_graph_root(g)
        amr = penman.AMRCodec().encode(g)
        print amr
        print amr2fol(amr)


