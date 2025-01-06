from setuptools import setup

setup(
    name='LeanPy',
    version='0.1.0',
    description='A Lean4 type checker in Python',
    author='Job Petrovčič',
    license='MIT',
    license_files=['LICENSE'],
    install_requires=[
        'typeguard',
        'typing',
    ],
    package_data={"LeanPy": ["py.typed"]},
    zip_safe=False,  
)
