 
import setuptools

with open("README.md", "r") as fh:
    long_description = fh.read()

setuptools.setup(
    name="pycosa", 
    version="0.1",
    author="smba",
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
