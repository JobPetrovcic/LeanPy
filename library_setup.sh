set -e # Exit on error

rm stubs/* -rf
stubgen -o stubs
python3 setup.py sdist bdist_wheel
pip install -e .