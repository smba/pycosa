from typing import Sequence
import z3

class FeatureModel:
    
    def __init__(self):
        pass
    
    @staticmethod
    def create(path: str):
        clauses, feature_dict = FeatureModel.__parse_dimacs(path)
    
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
    def __convert_dimacs_to_bool_model(dimacs: Sequence[Sequence[int]], features: dict) -> (Sequence[z3.Or], dict):
        '''
        :param dimacs:
        :param features:
        :return:
        '''
    
        clauses = []
    
        # create bool literals for each feature
        # index corresponds to the number used in the dimacs clauses
        literals = {index : z3.Bool(features[index]) for index in features}
    
    
        # add clauses of variability model        
    
        for clause in dimacs:
            c = []
            for opt in clause:
                if opt >= 0:                    # Feature opt is selected
                    c.append(literals[opt])
                else:                           # Feature opt is not selected
                    negated = z3.Not(literals[abs(opt)])
                    c.append(negated)
    
            clauses.append(z3.Or(c))
    
        return clauses, literals

    @staticmethod
    def __convert_dimacs_to_bit_model(dimacs: Sequence[Sequence[int]], n_options: int) -> (Sequence[z3.Or], z3.BitVec):
        '''
        :param dimacs:
        :param n_options:
        :return:
        '''
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
    
        return clauses, target#


class BooleanFeatureModel(FeatureModel):
    def __init__(self):
        pass
    
class BitFeatureModel(FeatureModel):
    def __init__(self):
        pass


