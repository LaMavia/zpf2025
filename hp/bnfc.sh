#!/usr/bin/env bash

cd $(dirname $0)
cd app 

if [ ! -f .cf ]; then
  echo "Missing .cf file, exiting"
  exit 1
fi

bnfc --functor --haskell --make .cf && make
