#!/bin/bash

go tool goose -out code -dir ../pav \
    ./advrpc ./alicebob ./auditor ./client ./cryptoffi ./cryptoutil \
    ./hashchain ./ktcore ./merkle ./netffi ./safemarshal ./server
go tool proofgen -out generatedproof -configdir code -dir ../pav \
    ./advrpc ./alicebob ./auditor ./client ./cryptoffi ./cryptoutil \
    ./hashchain ./ktcore ./merkle ./netffi ./safemarshal ./server
