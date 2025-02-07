# PyLean

PyLean is an external Python typechecker for Lean 4.

## Installation

Clone the repository and install the package:

```
pip install .
```

## Input Formats

The typechecker accepts two formats:
- **lean4export:** Refer to [LeanPy/Parsing/Lean4ExportParser.py](LeanPy/Parsing/Lean4ExportParser.py) (see branch *LeanPyFormat*).
- **JSON:** Lean code can be converted to JSON via the [lean4export repository](https://github.com/JobPetrovcic/lean4export/) (see branches *json*).

## Minimal Example: Compiling a Declaration in LeanPyFormat
After installing the library, put the file example_declaration.export into the same file as the following script.

```python
from LeanPy.Parsing.Lean4ExportParser import Lean4ExportParser

parsed = Lean4ExportParser.from_file("example_declaration.export")
```

Run the python script.

## Minimal Example: Compiling a Declaration in JSON Format
After installing the library and putting the example_declaration.json file in the directory, the declaration can be checked using:
```python
from LeanPy.Parsing.DependencyManager import DependencyManager

directory = "path/to/json/dumped/entries"

dp = DependencyManager(directory)
dp.load_and_check("example_declaration", should_dependencies_be_checked=False)
```

Run the python script.

> **Note:** Ensure that all other dependencies of the declaration are available in the specified directory.