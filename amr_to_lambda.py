#!/usr/bin/python2.7
# -*- coding: utf-8 -*-
"""
AMR transformer to first order logic expressions
implementation of Bos, J. Expressive Power of Abstract Meaning Representations, ACL, 2016.
"""
__author__ = 'papagandalf'

from amr import AMR
from nltk.sem.logic import *

def readAmrLine(file):
	soFar = ''
	for line in amrInput:
		line = line
		if line.strip() == '':
			break
		elif not line.startswith('#'):
			soFar = soFar + line	
	return soFar

def amIProjective(var, wholeAmr):
	iAmProjective = False
	inAnyOtherNode = [x for x in wholeAmr.links if var in x]
	if len(inAnyOtherNode) == 1:
		if len(inAnyOtherNode[0][var]) > 1:
			iAmProjective = True
	elif len(inAnyOtherNode) > 1:
		iAmProjective = True
	return iAmProjective

def normalizePredicateName(predicateName):
	predicateName = predicateName.strip()
	if predicateName == 'and':
		predicateName = 'AND'
	elif predicateName == 'or':
		predicateName = 'OR'
	elif predicateName == 'some':
		predicateName = 'SOME'
	elif predicateName == 'op1':
		predicateName = 'OP1'
	elif predicateName == 'all':
		predicateName = 'ALL'
	if len(predicateName) == 1:
		predicateName = '_{}_'.format(predicateName)
	return predicateName.replace('-', '_')

def normalizeConstant(const):
	const = const.replace('.', '_DOT_').replace('-', '_')
	return const
	

def lambdaAmr(amr, phi, wholeAmr, fromProjective=False):
	var = amr.nodes[0]
	allLinks = amr.links[0]
	allLinks.update(amr.const_links[0])
	negative = False
	if 'polarity' in amr.const_links[0] and amr.const_links[0]['polarity'][0] == '-':
		negative = True
		allLinks.pop('polarity')

	listOfFutureProjectivevars = []
	if len(allLinks) == 0:
		# simple AMR
		lambdaString = "exists {0}.{1}({0}) & {2}({0})".format(var, normalizePredicateName(amr.var_values[0]), phi)
	else:
		# complex AMR
		lambdaString = ''
		if negative:
			lambdaString = "-"
		lambdaString += 'exists {0}.({1}({0})'.format(var, normalizePredicateName(amr.var_values[0]))

		iAmProjective = amIProjective(var, wholeAmr)
		if iAmProjective and not fromProjective:
			return "{0}({1})".format(phi, var)
		for theVar, rels in allLinks.iteritems():
			for rel in rels:
				if rel != 'TOP':
					if amIProjective(theVar, wholeAmr) and not (any([x for x in wholeAmr.const_links if theVar in x])):
						listOfFutureProjectivevars.append(theVar)
					if theVar in amr.nodes and (not iAmProjective or fromProjective):
						whichNode = amr.nodes.index(theVar)
						partAMR = AMR(amr.nodes[whichNode:], amr.var_values[whichNode:], amr.links[whichNode:], amr.const_links[whichNode:], amr.path2label)
						partLambda = lambdaAmr(partAMR, '\y.{0}({1},y)'.format(normalizePredicateName(rel), var), wholeAmr, fromProjective)
						lambdaString += " & {}".format(partLambda)
					elif theVar in amr.const_links[0]:
						partLambda = '{1}({0}, {2})'.format(var, normalizePredicateName(theVar), normalizeConstant(rel))
						lambdaString += ' & {0}'.format(partLambda)
		lambdaString += " & {0}({1}))".format(phi, var)

	# add the lambda variables needed
	if len(listOfFutureProjectivevars) > 0:
		lambdaString = '\{0}.{1}'.format(" ".join(list(set(listOfFutureProjectivevars))), lambdaString)
	return lambdaString

def lambdaAmrProjective(amr, wholeAmr):
	if type(amr) is str:
		return '(\P1.P1)'

	var = amr.nodes[0]
	allLinks = amr.links[0]
	allLinks.update(amr.const_links[0])

	negative = False
	if 'polarity' in amr.const_links[0] and amr.const_links[0]['polarity'] == '-':
		negative = True
		allLinks.pop('polarity')

	if len(amr.nodes) == 1 and len(allLinks) == 0:
		return '(\P1.P1)'

	iAmProjective = amIProjective(var, wholeAmr)

	if len(amr.links[0]) == len(amr.const_links[0]):
		# simple AMR
		if iAmProjective:
			# i am x \ P (projective)
			lambdaString = '(\P1.({0}))'.format(lambdaAmr(amr, r'(\{0}.P1({0}))'.format(var), wholeAmr, True))
		else:
			# i am x / P (non-projective)
			lambdaString = '(\P1.P1)'
	else:
		# complex AMR
		lambdaString = ''		
		if iAmProjective:
			# i am x \ P (projective)
			lambdaString = '(\P1.({0}))'.format(lambdaAmr(amr, r'(\{0}.P1)'.format(var), wholeAmr))
		else:
			# I am x / P (normal, non-projective)
			lambdaString = '\P2.'
			for (theVar, rels) in [(x,allLinks[x]) for x in reversed(allLinks.keys())]:
				for rel in rels:
					if rel != 'TOP':
						if theVar in amr.nodes:
							whichNode = amr.nodes.index(theVar)
							partAMR = AMR(amr.nodes[whichNode:], amr.var_values[whichNode:], amr.links[whichNode:], amr.const_links[whichNode:], amr.path2label)
						else:
							partAMR = theVar
						lambdaString += '{0}('.format(lambdaAmrProjective(partAMR, wholeAmr))
			lambdaString += '(P2)'
			
			for theVar, rels in allLinks.iteritems():
				for rel in rels:
					if rel != 'TOP':
						lambdaString += ')'
	return lambdaString

# AMR dataset is distributed by LDC
with open('amr_test.txt', 'r') as amrInput:
	logicParser = LogicParser()
	soFar = ''
	oneBlank = False
	amrsRead = 0
	for line in amrInput:
		amrString = readAmrLine(amrInput)
		if amrString != '':
			amrsRead += 1
			amr = AMR.parse_AMR_line(amrString)
			assertivePart = lambdaAmr(amr, '\u.T', amr)
			assertiveL = logicParser.parse(assertivePart).simplify()
			print unicode(amrString, 'utf-8')
			print "\n"
			print unicode("assertiveL: {}".format(assertiveL), 'utf-8')
			projectivePart = lambdaAmrProjective(amr, amr)
			projectiveL = logicParser.parse(projectivePart).simplify()
			print unicode("projectiveL: {}".format(projectiveL), 'utf-8')
			final = logicParser.parse('({0})({1})'.format(projectiveL, assertiveL))
			print unicode("final simplified: {}".format(final.simplify()), 'utf-8')
			print "\n\n"
