import os
from Parsing.DependencyManager import DependencyManager

if __name__ == "__main__":
    dir ="../../lean2json/TestJSONProject/json_dump"
    ##LeanJSONParser.from_file(dir + "Bool.false.json")
    #for file in os.listdir(dir):
    #    print(f"parsing {file}")
    #    LeanJSONParser.from_file(dir + file)

    dp = DependencyManager(dir)

    for file in os.listdir(dir):
        decl_file_name = file[:-5]
        if not dp.is_loaded(decl_file_name):
            print(f"loading {decl_file_name}")
            dp.load(decl_file_name)

    