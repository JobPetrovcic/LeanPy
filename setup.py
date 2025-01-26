from setuptools import setup, find_packages

setup(
    name='LeanPy',
    version='1.0',
    packages=find_packages(),
    install_requires=[
        'typeguard',
        'typing_extensions'
    ],
    extras_require={
        'dev': ['mypy', 'pytest', 'stubgen'],
    },
    package_data={
        'LeanPy': ['*.pyi', 'py.typed']
    },
    zip_safe=False,  # Required for packages with type hints
)
