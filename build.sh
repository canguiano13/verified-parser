#!/bin/bash

#no need to rebuild
if [[ -d "./parse_ast-py"  && -e "./main.py" ]]; then
    echo "Dafny project already built. No need to rebuild."

    #just relink the driver
    echo -ne "Relinking...\r"
    cp driver.py parse_ast-py/
    ln -sf parse_ast-py/driver.py main.py 2>/dev/null
    echo -e "\t\tdone.\n"
    echo "Try parsing an expression!"
    echo "e.g. python3 main.py \"(+ 1 2 (- 4 3))\""

    exit 0 
fi

echo -n "Verifying and transpiling..."
#compile the dafny files into python
dafny build --target:py --output:parse_ast parser.dfy lexer2.dfy types.dfy validate.dfy

#check that dafny could compile the files
#build should have completed with exit code 0
#and should have added a target folder
if [[ ! $? == 0 || ! -d "./parse_ast-py" ]]; then
    echo "Build failed. Try again or try building manually (see README.md)."
     exit 1
fi

#copy driver into the folder for built project
echo -ne "Linking driver.py...\r";
cp driver.py ./parse_ast-py/

#then make a link to the file in that directory
ln -s parse_ast-py/driver.py main.py 

#make sure that the link exists, otherwise can't run
if [ ! -e "./main.py" ]; then
    echo "Build failed. Try again or try building manually (see README.md)."
    exit 1
fi
echo -e "\t\t\tdone.\n";

#now we can start parsing expressions
echo "Build was successful. Try parsing an expression!"
echo "e.g. python3 main.py \"(+ 1 2 (- 4 3))\""
