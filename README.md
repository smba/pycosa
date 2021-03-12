# pycosa [![Build Status](https://travis-ci.org/smba/pycosa.svg?branch=main)](https://travis-ci.org/smba/pycosa)
This is a collection of sampling strategies for (binary) configuration spaces. The algorithms implemented here are merely intended for demonstration and teaching purposes. A more mature tool box that has been widely used for congfiguration sampling is [SPLConqueror](https://github.com/se-sic/SPLConqueror).
## Documentation
### Feature Models

#### Input Formats
##### DIMACS
#### Internal Representation
##### Boolean Expression
##### Bit Vectors

### Sampling Strategies
#### Main Effects Sampling
```python
class CoverageSampler:
```
##### t-wise Sampling
##### Negative t-wise Sampling

#### Random Sampling
##### Solver-based Random Sampling
##### Sampling with Diversity Promotion
##### Distance-based Sampling
##### Sampling with Binary Decision Diagrams (BDD)
The original approach is outlined in the following paper: [_Finding near-optimal configurations in product lines by random sampling_](https://doi.org/10.1145/3106237.3106273)

#### Importance Sampling

## Technical
### Install
```
pip install git+https://github.com/smba/pycosa.git@main
```

### Build Status
* main [![Build Status](https://travis-ci.org/smba/pycosa.svg?branch=main)](https://travis-ci.org/smba/pycosa)
* dev
