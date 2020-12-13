# /bin/sh

echo "running goto-cc"
../../../build/bin/goto-cc -o foo.gb foo.c
../../../build/bin/goto-cc -o main.gb main.c
../../../build/bin/goto-cc -o all.gb foo.gb main.gb

echo "Printing the result"
../../../build/bin/goto-instrument --show-goto-functions all.gb
#../../../build/bin/goto-instrument --show-goto-functions foo.gb


echo "running goto-instrument"
../../../build/bin/goto-instrument --replace-all-calls-with-contracts all.gb all-mod.gb
# ../../../build/bin/goto-instrument --replace-all-calls-with-contracts foo.gb foo-mod.gb

echo "running goto-instrument to print out"
../../../build/bin/goto-instrument --show-goto-functions all-mod.gb

echo "running CBMC"
../../../build/bin/cbmc --trace all-mod.gb