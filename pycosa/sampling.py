'''
Created on Nov 12, 2020

@author: stefan
'''
import z3
import numpy as np
import pandas as pd

from pycosa.features import FeatureModel
import logging
import warnings
import itertools

class Sampler:
    
    def __init__(self, fm):
        self.fm = fm

class CoverageSampler:
    '''
    
    
    '''
    
    def __init__(self, fm):
        '''
        Constructor
        '''
        self.fm = fm
        
    def sample(self, t: int, negwise: bool = False):
        n_options = len(self.fm.feature_dict)
  
        clauses = self.fm.clauses
        target = self.fm.target
        
        clauses = z3.And(clauses)
    
        solutions = []
        for interaction in itertools.combinations(np.arange(n_options), t):
            optimizer = z3.Optimize()
            
            # assertions
            optimizer.add(clauses)
            for solution in solutions:
                optimizer.add(solution != target)
            
            for opt in interaction:
                opt = opt.item()
                
                if not negwise:
                    constraint = z3.Extract(opt, opt, target) == 1
                else:
                    constraint = z3.Extract(opt, opt, target) == 0
                    
                optimizer.add(constraint)
            
            func = z3.Sum([z3.ZeroExt(n_options, z3.Extract(i, i, target)) for i in range(n_options)])
            
            if not negwise:
                optimizer.minimize(func)
            else:
                optimizer.maximize(func)
            
            if optimizer.check() == z3.sat:
                solution = optimizer.model()[target]
                optimizer.add(solution != target)
                solutions.append(solution)
        
        solutions = [FeatureModel.int_to_config(solution.as_long(), n_options) for solution in solutions]
        solutions = np.vstack(solutions) == 1
        solutions = pd.DataFrame(solutions, columns = list(self.fm.feature_dict.values()))
    
        return solutions
    
    
class DistanceSampler:
    
    def __init__(self, fm: FeatureModel):
        self.fm = fm
    
    def sample(self, size: int):
        
        n_options = len(self.fm.feature_dict)
        origin = z3.BitVecVal("0" * n_options, n_options)
  
        clauses = self.fm.clauses
        target = self.fm.target
        
        clauses = z3.And(clauses)
        
        solvers = {i: z3.Solver() for i in range(1, n_options)}
        for index in solvers.keys(): 
            solvers[index].add(clauses)
            solvers[index].add(DistanceSampler.__hamming(origin, target, 1) == index)
            
        # set of existing solutions
        solutions = []
        
        # unsatisfiable distances
        available_distances = list(range(1, n_options))
        unsatisfiable = False
        sample_sized_reached = False
        
        while not (unsatisfiable or sample_sized_reached):
            distance = np.random.choice(available_distances)

            if solvers[distance].check() == z3.sat:
                solution = solvers[distance].model()[target]
                solvers[distance].add(target != solution)
                solutions.append(solution)
            else:
                available_distances.remove(distance)
    
            unsatisfiable = (len(available_distances) == 0)
            sample_sized_reached = (len(solutions) == size)
                    
        solutions = [FeatureModel.int_to_config(solution.as_long(), n_options) for solution in solutions]
        solutions = np.vstack(solutions) == 1
        solutions = pd.DataFrame(solutions, columns = list(self.fm.feature_dict.values()))
    
        return solutions
    
    @staticmethod
    def __hamming(V1, V2, target):
        h = V1 ^ V2
        s = max(target.bit_length(), V1.size().bit_length())
        return z3.Sum([z3.ZeroExt(s, z3.Extract(i, i, h)) for i in range(V1.size())])


a = FeatureModel("fm", "/home/stefan/eclipse-workspace/density-converter-model/model.dimacs")
b = CoverageSampler(a)
sample = b.sample(1)
print(sample)
import matplotlib.pyplot as plt
plt.pcolormesh(sample)
plt.show()
