import penman
import re


VARIABLE_NAME_RE = re.compile(r'^[a-zA-Z]\d*$')

def rename_variable(g, old_variable_name, new_variable_name):
    assert isinstance(g, penman.Graph)
    assert new_variable_name not in g.variables(), "{0} variable already in graph {1}".format(new_variable_name, g)
    if old_variable_name not in g.variables():
        return g
    if g.top == old_variable_name:
        new_top = new_variable_name
    else:
        new_top = g.top
    old_triples = g._triples
    new_triples = []
    for old_triple in old_triples:
        if old_triple.source == old_variable_name:
            assert old_triple.target != old_variable_name
            new_triple = penman.Triple(new_variable_name, old_triple.relation, old_triple.target, inverted=old_triple.inverted)
        elif old_triple.target == old_variable_name:
            assert old_triple.source != old_variable_name
            new_triple = penman.Triple(old_triple.source, old_triple.relation, new_variable_name, inverted=old_triple.inverted)
        else:
            new_triple = old_triple
        new_triples.append(new_triple)
    return penman.Graph(data=new_triples, top=new_top)

def rename_variables(g):
    assert isinstance(g, penman.Graph)
    old_variable_names = g.variables()
    new_variable_names = dict()
    i = 0
    for var in old_variable_names:
        if not VARIABLE_NAME_RE.match(var):
            while "z{}".format(i) in old_variable_names or "z{}".format(i) in new_variable_names.values():
                i += 1
            new_variable_names[var] = "z{}".format(i)
    new_graph = g
    for var in new_variable_names:
        new_graph = rename_variable(new_graph, var, new_variable_names[var])
    return new_graph
