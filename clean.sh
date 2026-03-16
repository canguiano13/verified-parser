#!/bin/bash

if [[ ! -f "./main.py" && ! -d "./parse_ast-py" ]]; then
    echo "Nothing to clean."
    exit 0
fi

#remove the link
rm main.py

#remove all the files in the built project
rm -r ./parse_ast-py/
