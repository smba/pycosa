from typing import Sequence
import logging
import z3
import numpy as np
import random 
from bitarray.util import int2ba
from numpy import dtype

import networkx as nx
from pyeda.inter import expr, expr2bdd

class FeatureModel(object):

    def __init__(self, src: str, shuffle_seed: int = 0, mode: str = 'bitvec'):

        self.mode = mode
        self.clauses_raw, self.feature_dict = FeatureModel.__parse_dimacs(src)
                
        if mode == 'bitvec':
            self.clauses, self.target = FeatureModel.__convert_dimacs_to_bitvec(self.clauses_raw, len(self.feature_dict))
        elif mode == 'bool':
            self.clauses = self._dimacs_to_boolean()
        else:
            logging.warn('Must select either Bitcevtor mode or Boolean mode')

    def shuffle(self, random_seed: int = 0):
        """
        Re-shuffles the composition of the feature model CNF
        """
        # shuffle feature model clauses (used for div. promotion)
        random.seed(random_seed)
        clauses_ = []
        for clause in self.clauses_raw:
            clause_ = random.sample(clause, len(clause))
            clauses_.append(clause_)
        clauses = random.sample(clauses_, len(clauses_))
            
        self.clauses, self.target = FeatureModel.__convert_dimacs_to_bitvec(clauses, len(self.feature_dict))

    def _dimacs_to_boolean(self):
        clauses = []
        for clause in self.clauses_raw:
            clauses.append(z3.Or([
                z3.Bool(self.feature_dict[abs(l)]) if l > 0 else z3.Not(z3.Bool(self.feature_dict[abs(l)])) for l in clause
            ]))
        return z3.And(clauses)

    @staticmethod
    def _dimacs_to_str(dimacs, literals):
        literal = lambda l: "~" + literals[-1 * l] if l < 0 else literals[l]# + str(l)
        clause = lambda c: "(" + " | ".join(list(map(literal, c))) + ")"
        cnf = " & ".join(list(map(clause, dimacs)))

        return cnf

    @staticmethod
    def _compute_partitions(expression, features):
        expression = expr(expression)
        bdd = expr2bdd(expression)
        dotrep = bdd.to_dot()
        start = dotrep.find('{') + 2
        end = dotrep.find('}') - 1
        entities = dotrep[start:end].split(';')

        nodes = list(filter(lambda x: 'shape' in x, entities))
        nnodes = {}
        for node in nodes:
            node = node.strip()
            name = node.split(' ')[0]
            label = node.split(' ')[1][1:-1].split(',')[0].replace('label=', '').replace('"', '')
            nnodes[name] = label

        edges = list(filter(lambda x: '--' in x, entities))

        nedges = {}
        for edge in edges:
            edge = edge.strip()
            fromto = tuple(edge.split(' [')[0].split(' -- '))
            label = int(edge.split(' [')[1][6:7])
            nedges[fromto] = label

        G = nx.DiGraph()

        for node in nnodes:
            G.add_node(node)

        for edge in nedges:
            G.add_edge(edge[0], edge[1])

        # start node is the node from which edges start, but to which no edge leads
        start_nodes = set([edge[0] for edge in nedges])
        end_nodes = set([edge[1] for edge in nedges])

        start_node = list(start_nodes - end_nodes)[0]
        end_node = list(filter(lambda x: nnodes[x] == '1', nnodes))[0]

        frequencies = {feature: 0 for feature in features}
        partitions = []
        overall_size = 0
        for path in nx.all_simple_edge_paths(G, start_node, end_node):
            partition_size = 2**(len(features) - len(path))
            partition = {}
            overall_size += partition_size
            for edge in path:
                partition[nnodes[edge[0]]] = bool( nedges[edge] )
            partitions.append(partition)
        return partitions

    def _compute_frequencies(self):
        '''
        Computes the frequency of configurations with each feature or interaction enabled.
        '''
        pass

    @staticmethod
    def __parse_dimacs(path: str) -> (Sequence[Sequence[int]], dict):
        '''
        :param path:
        :return:
        '''
    
        dimacs = list()
        dimacs.append(list())
        with open(path) as mfile:
            lines = list(mfile)
    
            # parse names of features from DIMACS comments (lines starting with c)
            feature_lines = list(filter(lambda s: s.startswith("c"), lines))
            feature_names = dict(map(lambda l: (int(l.split(" ")[1]), l.split(" ")[2].replace("\n", "")), feature_lines))
    
            # remove comments
            lines = list(filter(lambda s: not s.startswith("c"), lines))

            for line in lines:
                tokens = line.split()
                if len(tokens) != 0 and tokens[0] not in ("p", "c"):
                    for tok in tokens:
                        lit = int(tok)
                        if lit == 0:
                            dimacs.append(list())
                        else:
                            dimacs[-1].append(lit)
            assert len(dimacs[-1]) == 0
            dimacs.pop()
        
        return dimacs, feature_names
    
    @staticmethod
    def __convert_dimacs_to_bitvec(dimacs: Sequence[Sequence[int]], n_options: int) -> (Sequence[z3.Or], z3.BitVec):
        
        clauses = []
        target = z3.BitVec('target', n_options)

        # add clauses of variability model
        for clause in dimacs:
            c = []
            for opt in clause:
                opt_sign = 1 if opt >= 0 else 0
                optid = n_options - abs(opt)
                c.append(z3.Extract(optid, optid, target) == opt_sign)
    
            clauses.append(z3.Or(c))
    
        return clauses, target
    
    @staticmethod
    def config_to_int(config: np.ndarray) -> int:
        '''
        :param config:
        :return:
        '''
        pass
    
    @staticmethod
    def int_to_config(i: int, n_options: int) -> np.ndarray:
        '''
        :param i:
        :param n_options:
        :return:
        '''

        without_offset = np.array([int(x) for x in np.binary_repr(i)])
        offset = n_options - len(without_offset)
        binary = np.append(np.zeros(dtype=int, shape=offset), without_offset)
        
        return binary


