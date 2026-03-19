#!/bin/bash

#no need to rebuild
if [[ -d "./parse_ast-py"  && -e "./main.py" ]]; then
    echo "Already built. No need to rebuild."
    exit 0 
fi

#compile the dafny files into python
dafny build --target:py --output:parse_ast parser.dfy lexer.dfy types.dfy validate.dfy

#check that dafny could compile the files
if [ ! -d "./parse_ast-py" ]; then
    echo "Build failed. Try again or try building manually (see README)?"
     exit 1
fi

#copy main into the folder for built project
cp driver.py parse_ast-py/

#then make a link to the file in that directory
#file might already exist, so just send error output to null
ln -s parse_ast-py/driver.py main.py 2>/dev/null

#make sure that the link exists, otherwise can't run
if [ ! -e "./main.py" ]; then
    echo "Build failed. Try again or try building manually (see README)?"
    exit 1
fi

#now we can start parsing expressions
echo "Build was successful. Try parsing an expression!"
echo "e.g. python3 main.py \"(+ 1 2 (- 4 3))\""
