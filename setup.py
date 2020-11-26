 
import setuptools

with open("README.md", "r") as fh:
    long_description = fh.read()

setuptools.setup(
    name="smba", 
    version="0.0.1",
    author="Stefan Mühlbauer",
    author_email="",
    description="configuration sampling in python",
    long_description=long_description,
    long_description_content_type="text/markdown",
    url="https://github.com/smba/pycosa",
    packages=setuptools.find_packages(),
    classifiers=[
        "Programming Language :: Python :: 3",
        "License :: OSI Approved :: MIT License",
        "Operating System :: OS Independent",
    ],
    python_requires='>=3.6',
)
