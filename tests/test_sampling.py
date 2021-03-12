from unittest import TestCase

import pandas as pd
import matplotlib.pyplot as plt
import numpy as np
import itertools

from pycosa.features import FeatureModel
from pycosa.sampling import DiversityPromotionSampler, NaiveRandomSampler, DistanceSampler


class TestImportanceDistributionSampler(TestCase):

    def setUp(self):
        pass

    def test_compute_distribution(self):
        fm = FeatureModel(src='feature_models/h2.dimacs')
        literals = fm.feature_dict

        dimacs = fm.clauses_raw
        expr = FeatureModel._dimacs_to_str(dimacs, literals)

        overall = FeatureModel._compute_partition(expr, literals.values())

        for part in overall:
            for term in part:
                print(term)
            print('-------')



