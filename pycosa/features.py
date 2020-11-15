from typing import Sequence
import logging
import z3
import numpy as np

class FeatureModel(object):
    '''
    
    '''

    def __init__(self, src: str):

        clauses, feature_dict = FeatureModel.__parse_dimacs(src)

        self.clauses, self.target = FeatureModel.__convert_dimacs_to_bitvec(clauses, len(feature_dict))
        self.feature_dict = feature_dict
        
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
    
            # remove comments
    
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
    
        
    
        offset = n_options - int(np.ceil(np.log2(i)))
        binary_string = "0" * offset + str(bin(i))[2:]
        assert(len(binary_string) == n_options)
    
        binary = np.array([int(bit) for bit in binary_string])
        return binary
