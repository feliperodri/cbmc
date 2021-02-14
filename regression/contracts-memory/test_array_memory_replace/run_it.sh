# /bin/sh

echo "running goto-cc"
../../../build/bin/goto-cc -o main.gb main.c

echo "running goto-instrument"
../../../build/bin/goto-instrument --replace-all-calls-with-contracts main.gb main-mod.gb
# ../../../build/bin/goto-instrument --replace-all-calls-with-contracts foo.gb foo-mod.gb

echo "running goto-instrument to print out"
../../../build/bin/goto-instrument --show-goto-functions main-mod.gb

echo "running CBMC"
../../../build/bin/cbmc --trace main-mod.gb